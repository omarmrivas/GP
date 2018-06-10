module RandomTerms

open System
open System.Numerics
open RandomBigInteger
open System.Collections.Generic
open FSharp.Quotations.Evaluator
open Microsoft.FSharp.Quotations
open Utils

type par_data = Random * (Type * (Type*bigint) list * int -> bigint)

type term = Free of string * System.Type
          | Lam of string * System.Type * term
          | App of term * term

let memoize fn =
//  let cache = new System.Collections.Concurrent.ConcurrentDictionary<_,_>()
  let cache = new System.Collections.Generic.Dictionary<_,_>()
  (fun x ->
    match cache.TryGetValue x with
    | true, v -> v
    | false, _ -> let v = fn (x)
                  cache.[x] <- v
                  v)

(* Counting of terms *)

let type_cnt (env : (System.Type * bigint) list) A =
    match List.tryFind (fun (typ, _) -> A.ToString() = typ.ToString()) env with
        | Some (_, c) -> c
        | None -> bigint 0

let type_cnt_inc (env : (System.Type * bigint) list) A =
    env |> List.fold (fun (env,updated) (typ, c) ->
                               if A.ToString() = typ.ToString()
                               then (env @ [(typ, c + bigint 1)], true)
                               else (env @ [(typ, c)], updated)) ([],false)
        |> (fun (env, updated) -> if updated 
                                  then env
                                  else env @ [(A, bigint 1)])

let var_type A = 
    match strip_type A with
        ([], _) -> true
        | _ -> false

let arrow_type A = 
    match strip_type A with
        ([], _) -> false
        | _ -> true

let valid_head_var_type_set (A:System.Type) (env : (System.Type * bigint) list) =
    let rec check_head bis (typ:System.Type) =
            if typ.ToString() = A.ToString() then Some bis
            else try
                    check_head (bis @ [domain_type typ]) (range_type typ)
                 with :? System.ArgumentException -> None
    List.choose
          (fun (typ,_) ->
                     match check_head [] typ with
                         Some bis -> Some (bis, typ)
                       | None -> None) env

let ndk n k =
    if k < 1 || n < 1 || n < k then []
    else let offset = n - k + 2
         let max_elements = [for i in 1 .. k do yield offset]
         let index_elements = [for i in 1 .. k - 1 do yield 0] @ [-1]
         let rec sumatories R index =
               match next_digit max_elements index with
                 Some index ->
                     let elements = List.map (fun i -> i + 1) index
                     let sum = List.sum elements
                     if sum = n then sumatories (elements :: R) index
                     else sumatories R index
               | None -> R
         sumatories [] index_elements

let rec count_term' A env s =
    if s < 1 then bigint 0
    else if s = 1 then type_cnt env A
    else if var_type A then count_head_var_term A env s
    else (count_term' (range_type A) (type_cnt_inc env (domain_type A)) (s - 1))
         + (count_head_var_term A env s)
and count_head_var_term A env s =
    List.fold (fun num_terms (bis, B) -> num_terms + count_head_var_arg_terms (bis, B) env s) (bigint 0) (valid_head_var_type_set A env)
and count_head_var_arg_terms (bis, B) env s =
    let num_var_with_type_in_env = type_cnt env B
    let m = List.length bis
    if num_var_with_type_in_env > bigint 0
    then num_var_with_type_in_env *
           (List.sumBy
              (fun Ss ->
                  let multipl = if List.isEmpty Ss then bigint 0
                                else Ss |> List.fold (fun (m,i) si -> (m * (count_term' (List.item i bis) env si), i + 1)) (bigint 1, 0)
                                        |> fst
                  multipl) (ndk (s - 1 - m) m))
    else bigint 0

let count_term =
    memoize (fun (A,env,s) -> count_term' A env s)

(*let count_term (A,env,s) = count_term' A env s*)

let count_terms A s = count_term (A, [], s)

(* Random generation of terms *)

let choose_arg_size ((rnd, count_term) : par_data) (bis, B) env s num_arg_terms =
//      printfn "choose_arg_size"
      let rand_num = RandomIntegerBelow rnd num_arg_terms
      let m = List.length bis
      let rec semi_fold num_terms L =
            match (num_terms, L) with
                | (_, []) -> failwith "Should not be thrown"
                | (num_terms, Ss :: list) ->
                    let multipl = if List.isEmpty Ss then bigint 0
                                  else Ss |> List.fold (fun (m,i) si -> (m * (count_term (List.item i bis, env, si)), i + 1)) (bigint 1,0)
                                          |> fst
                    let num_terms = num_terms + multipl
                    //considerar todos los Ss's que tengan a multipl > 0
                    if rand_num < num_terms then Ss
                    else semi_fold num_terms list
      semi_fold (bigint 0) (ndk (s - 1 - m) m)

let choose_head_var ((rnd, count_term) : par_data) A env s num_app_terms =
//      printfn "choose_head_var"
      let rand_num = RandomIntegerBelow rnd num_app_terms
//      printfn "choose_head_var(1)"
      let vset = valid_head_var_type_set A env
//      printfn "choose_head_var(2)"
      let rec semi_fold num_terms L =
            match (num_terms, L) with
                | (_, []) -> failwith "Should not be thrown"
                | (num_terms, (bis, B) :: list) ->
                    let count_head_var = count_head_var_arg_terms (bis, B) env s
                    let num_terms = num_terms + count_head_var
                    // Considerar todos los (Bis, B) cuyos count_head_var sea mayor que 0 
                    if rand_num < num_terms
                    then ((bis, B), choose_arg_size (rnd, count_term) (bis, B) env s (count_head_var / (type_cnt env B)))
                    else semi_fold num_terms list
      semi_fold (bigint 0) (valid_head_var_type_set A env)

let gen_var_term (rnd : Random) A env =
//      printfn "choose_head_var"
      let tc = type_cnt env A
      let rand_num = RandomIntegerBelow rnd tc
      if tc = bigint 0 then None
      else Some (Free ("x." + string (List.findIndex (fun (ty,_) -> A.ToString() = ty.ToString()) env) + "." + string rand_num, A))

let rec gen_term ((rnd, count_term) : par_data) A env s =
//      printfn "gen_term"
      if s < 1 then None
      else if s = 1 then
        if type_cnt env A > bigint 0 then gen_var_term rnd A env
        else None
      else if arrow_type A then
        let total_num_term = count_term (A, env, s)
        let num_lam_term = count_term (range_type A, type_cnt_inc env (domain_type A), s - 1)
        let rand_num = RandomIntegerBelow rnd total_num_term
        if total_num_term = bigint 0 then None
           else if rand_num < num_lam_term
           then Some (gen_lam_term (rnd, count_term) (domain_type A) (range_type A) env s)
           else Some (gen_app_term (rnd, count_term) A env s (total_num_term - num_lam_term))
      else Some (gen_app_term (rnd, count_term) A env s (count_term (A, env, s)))
and gen_lam_term ((rnd, count_term) : par_data) arg_typ res_typ env s =
//      printfn "gen_lam_term"
      let env = type_cnt_inc env arg_typ
      let name = "x." + string (List.findIndex (fun (ty,_) -> arg_typ.ToString() = ty.ToString()) env) + "." +
                     string (type_cnt env arg_typ - bigint 1)
      let body = gen_term (rnd, count_term) res_typ env (s - 1)
      Lam (name, arg_typ, Option.get body)
and gen_app_term ((rnd, count_term) : par_data) A env s num_app_terms =
//      printfn "gen_app_term"
      let ((bis, B), Ss) = choose_head_var (rnd, count_term) A env s num_app_terms
      let head_var = Option.get (gen_var_term rnd B env)
      let tis = List.map (fun (i,si) -> Option.get (gen_term (rnd, count_term) (List.item i bis) env si)) (List.mapi (fun i si -> (i, si)) Ss)
      List.fold (fun t ti -> App (t, ti)) head_var tis

let rec normalize_closed_term vars v =
    match v with
        | Free (n, _) ->
            vars |> List.find (fun (name, var) -> name = n)
                 |> snd
        | App (s, t) ->
            Expr.Application (normalize_closed_term vars s, normalize_closed_term vars t)
        | Lam (n, T, t) ->
            let var = Var (n, T)
            Expr.Lambda (var, normalize_closed_term ((n,Expr.Var var) :: vars) t)

let random_term par_data A s =
    match gen_term par_data A [] s with
      Some t -> Some (normalize_closed_term [] t)
    | None -> None

