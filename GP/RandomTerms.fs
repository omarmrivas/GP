﻿module RandomTerms

open System.Collections.Generic
open FSharp.Quotations.Evaluator
open Microsoft.FSharp.Quotations
open Utils

type term = Free of string * System.Type
          | Lam of string * System.Type * term
          | App of term * term


(* Counting of terms *)

let type_cnt (env : (System.Type * int) list) A =
    match List.tryFind (fun (typ, _) -> A.ToString() = typ.ToString()) env with
        | Some (_, c) -> c
        | None -> 0

let type_cnt_inc (env : (System.Type * int) list) A =
    env |> List.fold (fun (env,updated) (typ, c) ->
                               if A.ToString() = typ.ToString()
                               then (env @ [(typ, c + 1)], true)
                               else (env @ [(typ, c)], updated)) ([],false)
        |> (fun (env, updated) -> if updated 
                                  then env
                                  else env @ [(A, 1)])

let var_type A = 
    match strip_type A with
        ([], _) -> true
        | _ -> false

let arrow_type A = 
    match strip_type A with
        ([], _) -> false
        | _ -> true

let valid_head_var_type_set (A:System.Type) (env : (System.Type * int) list) =
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
    let offset = n - k + 2
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
    if k < 1 then []
    else if n < 1 then []
    else if n < k then []
    else sumatories [] index_elements

let rec count_term A env s =
    if s < 1 then 0
    else if s = 1 then type_cnt env A
    else if var_type A then count_head_var_term A env s
    else (count_term (range_type A) (type_cnt_inc env (domain_type A)) (s - 1))
         + (count_head_var_term A env s)
and count_head_var_term A env s =
    List.fold (fun num_terms (bis, B) -> num_terms + count_head_var_arg_terms (bis, B) env s) 0 (valid_head_var_type_set A env)
and count_head_var_arg_terms (bis, B) env s =
    let num_var_with_type_in_env = type_cnt env B
    let m = List.length bis
    if num_var_with_type_in_env > 0
    then num_var_with_type_in_env *
           (List.sumBy
              (fun Ss ->
                  let multipl = if List.isEmpty Ss then 0
                                else Ss |> List.fold (fun (m,i) si -> (m * (count_term (List.item i bis) env si), i + 1)) (1,0)
                                        |> fst
                  multipl) (ndk (s - 1 - m) m))
    else 0

let count_terms A s = count_term A [] s


(* Random generation of terms *)

let choose_arg_size (rnd : System.Random) (bis, B) env s num_arg_terms =
      let rand_num = rnd.Next num_arg_terms
      let m = List.length bis
      let rec semi_fold num_terms L =
            match (num_terms, L) with
                | (_, []) -> failwith "Should not be thrown"
                | (num_terms, Ss :: list) ->
                    let multipl = if List.isEmpty Ss then 0
                                  else Ss |> List.fold (fun (m,i) si -> (m * (count_term (List.item i bis) env si), i + 1)) (1,0)
                                          |> fst
                    let num_terms = num_terms + multipl
                    //considerar todos los Ss's que tengan a multipl > 0
                    if rand_num < num_terms then Ss
                    else semi_fold num_terms list
      semi_fold 0 (ndk (s - 1 - m) m)

let choose_head_var (rnd : System.Random) A env s num_app_terms =
      let rand_num = rnd.Next num_app_terms
      let vset = valid_head_var_type_set A env
      let rec semi_fold num_terms L =
            match (num_terms, L) with
                | (_, []) -> failwith "Should not be thrown"
                | (num_terms, (bis, B) :: list) ->
                    let count_head_var = count_head_var_arg_terms (bis, B) env s
                    let num_terms = num_terms + count_head_var
                    // Considerar todos los (Bis, B) cuyos count_head_var sea mayor que 0 
                    if rand_num < num_terms
                    then ((bis, B), choose_arg_size rnd (bis, B) env s (count_head_var / (type_cnt env B)))
                    else semi_fold num_terms list
      semi_fold 0 (valid_head_var_type_set A env)

let gen_var_term (rnd : System.Random) A env =
      let tc = type_cnt env A
      let rand_num = rnd.Next tc
      if type_cnt env A = 0 then None
//      else Some (Free ("x." + string rand_num, A))
      else Some (Free ("x." + string (List.findIndex (fun (ty,_) -> A.ToString() = ty.ToString()) env) + "." + string rand_num, A))
//      else Some (Free ("x" + string (!c), A))

let rec gen_term (rnd : System.Random) A env s =
      if s < 1 then None
      else if s = 1 then
        if type_cnt env A > 0 then gen_var_term rnd A env
        else None
      else if arrow_type A then
        let total_num_term = count_term A env s
        let num_lam_term = count_term (range_type A) (type_cnt_inc env (domain_type A)) (s - 1)
        let rand_num = rnd.Next total_num_term
        if total_num_term = 0 then None
           else if rand_num < num_lam_term
           then Some (gen_lam_term rnd (domain_type A) (range_type A) env s)
           else Some (gen_app_term rnd A env s (total_num_term - num_lam_term))
      else Some (gen_app_term rnd A env s (count_term A env s))
and gen_lam_term (rnd : System.Random) arg_typ res_typ env s =
      let env = type_cnt_inc env arg_typ
      let name = "x." + string (List.findIndex (fun (ty,_) -> arg_typ.ToString() = ty.ToString()) env) + "." +
                     string (type_cnt env arg_typ - 1)
      let body = gen_term rnd res_typ env (s - 1)
      Lam (name, arg_typ, Option.get body)
and gen_app_term (rnd : System.Random) A env s num_app_terms =
      let ((bis, B), Ss) = choose_head_var rnd A env s num_app_terms
      let head_var = Option.get (gen_var_term rnd B env)
      let tis = List.map (fun (i,si) -> Option.get (gen_term rnd (List.item i bis) env si)) (List.mapi (fun i si -> (i, si)) Ss)
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

let random_term (rnd : System.Random) A s =
    match gen_term rnd A [] s with
      Some t -> Some (normalize_closed_term [] t)
    | None -> None

