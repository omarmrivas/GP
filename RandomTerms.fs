module RandomTerms

open Library
open Term

let type_cnt env A =
    match Map.tryFind A env with
         Some c -> c
        | None -> 0

let type_cnt_inc env A =
    match Map.tryFind A env with
         Some c -> Map.add A (c + 1) env
        | None -> Map.add A 1 env

let var_type A = 
    match Term.strip_type A with
        ([], _) -> true
        | _ -> false

let arrow_type A = 
    match Term.strip_type A with
        ([], _) -> false
        | _ -> true

let valid_head_var_type_set A env =
    let rec check_head bis typ =
            if typ = A then Some bis
            else try
                    check_head (bis @ [domain_type typ]) (range_type typ)
                 with TYPE _ -> None
    Map.fold (fun r typ _ ->
                      match check_head [] typ with
                        Some bis -> (bis, typ) :: r
                      | None -> r) [] env

let ndk n k = 
    let offset = n - k + 2
    let max_elements = [for i in 1 .. k do yield offset]
    let index_elements = [for i in 1 .. k - 1 do yield 0] @ [-1]
    let rec sumatories R index =
          match next_digit max_elements index with
            Some index ->
                let elements = List.map (fun i -> i + 1) index
                let sum = List.sum elements //Library.foldl (fun (s, i) -> s + i) (0, elements)
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
    Library.foldl (fun (num_terms, (bis, B)) -> num_terms + count_head_var_arg_terms (bis, B) env s) (0, valid_head_var_type_set A env)
and count_head_var_arg_terms (bis, B) env s =
    let num_var_with_type_in_env = type_cnt env B
    let m = List.length bis
    if num_var_with_type_in_env > 0
    then num_var_with_type_in_env *
            (Library.foldl
               (fun (num_terms, Ss) ->
                   let multipl = if List.isEmpty Ss then 0
                                 else ((1,0), Ss) |> Library.foldl (fun ((m,i), si) -> (m * (count_term (List.item i bis) env si), i + 1))
                                                  |> fst
                   num_terms + multipl) (0, ndk (s - 1 - m) m))
       else 0

let count_terms A s = count_term A Map.empty s

let choose_arg_size (rnd : System.Random) (bis, B) env s num_arg_terms =
//      let rand_num = Library.rndNext(0, num_arg_terms - 1)
      let rand_num = Library.rndNext rnd (0, num_arg_terms)
      //printfn "choose_arg_size (0, %A): %A" (string (num_arg_terms - 1)) (string rand_num)
      let m = List.length bis
      let rec semi_fold num_terms L =
            match (num_terms, L) with
                | (_, []) -> failwith "Should not be thrown"
                | (num_terms, Ss :: list) ->
                    let multipl = if List.isEmpty Ss then 0
                                  else ((1,0), Ss) |> Library.foldl (fun ((m,i), si) -> (m * (count_term (List.item i bis) env si), i + 1))
                                                   |> fst
                    //printfn "multipl: %A" (string multipl)
                    let num_terms = num_terms + multipl
                    (* considerar todos los Ss's que tengan a multipl > 0 *)
                    if rand_num < num_terms then Ss
                    else semi_fold num_terms list
      semi_fold 0 (ndk (s - 1 - m) m)

let choose_head_var (rnd : System.Random) A env s num_app_terms =
//      let rand_num = Library.rndNext(0, num_app_terms - 1)
      let rand_num = Library.rndNext rnd (0, num_app_terms)
      let vset = valid_head_var_type_set A env
      //printfn "choose_head_var (0, %A): valid set size: %A - %A" (string (num_app_terms - 1)) (string (List.length vset)) (string rand_num)
      let rec semi_fold num_terms L =
            match (num_terms, L) with
                | (_, []) -> failwith "Should not be thrown"
                | (num_terms, (bis, B) :: list) ->
                    let count_head_var = count_head_var_arg_terms (bis, B) env s
                    let num_terms = num_terms + count_head_var
                    //printfn "count_head_var: %A" (string count_head_var)
                    (* Considerar todos los (Bis, B) cuyos count_head_var sea mayor que 0 *)
                    if rand_num < num_terms
                    then ((bis, B), choose_arg_size rnd (bis, B) env s (count_head_var / (type_cnt env B)))
                    else semi_fold num_terms list
      semi_fold 0 (valid_head_var_type_set A env)

//let index A = find_index (fun (typ, _) => typ = A)

let gen_var_term (rnd : System.Random) A env =
//      let tc = type_cnt env A - 1
      let tc = type_cnt env A
      let rand_num = Library.rndNext rnd (0, tc)
      //printfn "gen_var_term (0, %A): %A" (string tc) (string rand_num)
      if type_cnt env A = 0 then None
//      else Some (Free ("x." + string rand_num, A))
      else Some (Free ("x." + Term.typ_to_string A + "." + string rand_num, A))

let rec gen_term (rnd : System.Random) A env s =
      if s < 1 then None
      else if s = 1 then
        if type_cnt env A > 0 then gen_var_term rnd A env
        else None
      else if arrow_type A then
        let total_num_term = count_term A env s
        let num_lam_term = count_term (range_type A) (type_cnt_inc env (domain_type A)) (s - 1)
//        let rand_num = Library.rndNext(0, total_num_term - 1)
        let rand_num = Library.rndNext rnd (0, total_num_term)
        //printfn "gen_term (0, %A): num_lambda_terms: %A - %A" (string (total_num_term - 1)) (string num_lam_term) (string rand_num)
        if total_num_term = 0 then None
           else if rand_num < num_lam_term
           then Some (gen_lam_term rnd (domain_type A) (range_type A) env s)
           else Some (gen_app_term rnd A env s (total_num_term - num_lam_term))
      else Some (gen_app_term rnd A env s (count_term A env s))
and gen_lam_term (rnd : System.Random) arg_typ res_typ env s =
      let env = type_cnt_inc env arg_typ
//      let name = "x." + string (type_cnt env arg_typ - 1)
      let name = "x." + Term.typ_to_string arg_typ + "." +
                     string (type_cnt env arg_typ - 1)
      let body = gen_term rnd res_typ env (s - 1)
      Abs (name, arg_typ, Option.get body)
and gen_app_term (rnd : System.Random) A env s num_app_terms =
      let ((bis, B), Ss) = choose_head_var rnd A env s num_app_terms
      let head_var = Option.get (gen_var_term rnd B env)
      let tis = List.map (fun (i,si) -> Option.get (gen_term rnd (List.item i bis) env si)) (List.mapi (fun i si -> (i, si)) Ss)
      Library.foldl (fun (t, ti) -> App (t, ti)) (head_var, tis)

let rec normalize_term t =
   match t with
    | (Abs (name, T, t)) ->
        let t' = normalize_term t
        absfree (name, T) t'
    | App (p, q) -> App (normalize_term p, normalize_term q)
    | t -> t


let rec normalize_closed_term level vars names v =
    match v with
        | Free (n, _) ->
            vars |> List.find (fun (name, l) -> name = n)
                 |> (fun (name, l) -> Bound (level - l - 1))
        | App (s, t) ->
            App (normalize_closed_term level vars names s, normalize_closed_term level vars names t)
        | Abs (n, T, t) ->
            let name = singleton (Name.variant_list names) "x"
            Abs (name, T, normalize_closed_term (level + 1) ((n, level) :: vars) (name :: names) t)
        | _ -> failwith "Should not be thrown"

let random_term (rnd : System.Random) A s = 
    match gen_term rnd A Map.empty s with
      Some t -> Some (normalize_closed_term 0 [] [] t)
    | None -> None
