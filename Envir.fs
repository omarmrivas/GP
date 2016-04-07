
module Envir

open Same
open Term

type tenv = Map<indexname, typ * term>
type env = {maxidx: int; tenv: tenv; tyenv: tyenv}

let empty_env maxidx = {maxidx = maxidx; tenv = Map.empty; tyenv = Map.empty}

let norm_type0 tyenv : operation<typ> =
  let rec norm typ = 
      match typ with
        | Type (a, Ts) -> Type (a, map norm Ts)
        | TFree _ -> raise SAME
        | TVar (v,v') ->
          match lookup tyenv (v,v') with
            | Some U -> commit norm U
            | None -> raise SAME
  norm

let norm_type_same tyenv T =
  if Map.isEmpty tyenv then raise SAME
  else norm_type0 tyenv T


let norm_types_same tyenv Ts =
  if Map.isEmpty tyenv then raise SAME
  else map (norm_type0 tyenv) Ts


let norm_type tyenv T = try norm_type_same tyenv T with SAME -> T


(** beta normalization wrt. environment **)

(*Chases variables in env.  Does not exploit sharing of variable bindings
  Does not check types, so could loop.*)

let var_clash xi T T' =
  raise (TYPE ("Variable has two distinct types", [], [Var (xi, T'); Var (xi, T)]))

(*equality with respect to a type environment*)
let rec equal_type tye (T, T') =
  match (devar tye T, devar tye T') with
    | (Type (s, ts), Type (s', ts')) ->
       s = s' && List.forall2 (fun x y -> equal_type tye (x,y)) ts ts'
    | (U, U') -> U = U'

let eq_type tye =
  if Map.isEmpty tye then (fun (x,y) -> x = y) else equal_type tye


let lookup_check check tenv (xi, T) =
  match Map.tryFind xi tenv with
    | None -> None
    | Some (U, t) -> if check (T, U) then Some t else var_clash xi T U

let lookup1 tenv = lookup_check (fun (x,y) -> x = y) tenv

let lookup2 (tyenv, tenv) = lookup_check (eq_type tyenv) tenv


let norm_term1 tenv : Same.operation<term> =
  let rec norm t =
    match t with
        | Var (v,v') ->
          match lookup1 tenv (v,v') with
            | Some u -> Same.commit norm u
            | None -> raise Same.SAME
        | Abs (a, T, body) -> Abs (a, T, norm body)
        | App (Abs (_, _, body), t) -> Same.commit norm (subst_bound (t, body))
        | App (f, t) ->
          try
            match norm f with
                | Abs (_, _, body) -> Same.commit norm (subst_bound (t, body))
                | nf -> App (nf, Same.commit norm t)
          with Same.SAME -> App (f, norm t)
        | _ -> raise Same.SAME
  norm

let norm_term2 tenv tyenv : Same.operation<term> =
  let normT = norm_type0 tyenv
  let rec norm t =
      match t with
        | Const (a, T) -> Const (a, normT T)
        | Free (a, T) -> Free (a, normT T)
        | Var (xi, T) ->
          match lookup2 (tyenv, tenv) (xi, T) with
            | Some u -> Same.commit norm u
            | None -> Var (xi, normT T)
        | Abs (a, T, body) ->
          try
            Abs (a, normT T, Same.commit norm body)
          with Same.SAME -> Abs (a, T, norm body)
        | App (Abs (_, _, body), t) -> Same.commit norm (subst_bound (t, body))
        | App (f, t) ->
          try
            match norm f with
                | Abs (_, _, body) -> Same.commit norm (subst_bound (t, body))
                | nf -> App (nf, Same.commit norm t)
          with Same.SAME -> App (f, norm t)
        | _ -> raise Same.SAME
  norm

let norm_term_same ({tenv = tenv; tyenv = tyenv} : env) =
  if Map.isEmpty tyenv then norm_term1 tenv
  else norm_term2 tenv tyenv

(* full eta contraction *)

let rec decr lev t =
  match t with
    | Bound i -> if i >= lev then Bound (i - 1) else raise Same.SAME
    | Abs (a, T, body) -> Abs (a, T, decr (lev + 1) body)
    | App (t, u) -> try App (decr lev t, decrh lev u) with Same.SAME -> App (t, decr lev u)
    | _ -> raise Same.SAME
and decrh lev t = try decr lev t with Same.SAME -> t

let rec eta t =
  match t with
    | Abs (a, T, body) ->
      try
        match eta body with
            | App (f, Bound 0) as body' ->
                if Term.is_dependent f then Abs (a, T, body')
                else decrh 0 f
            | body' -> Abs (a, T, body')
      with Same.SAME ->
        match body with
            | App (f, Bound 0) ->
                if Term.is_dependent f then raise Same.SAME
                else decrh 0 f
            | _ -> raise Same.SAME
    | App (t, u) -> try App (eta t, Same.commit eta u)
                    with Same.SAME -> App (t, eta u)
    | _ -> raise Same.SAME

let eta_contract t =
  if Term.has_abs t then Same.commit eta t else t

let norm_term envir t = try norm_term_same envir t with Same.SAME -> t

let beta_norm t = if Term.has_abs t then norm_term (empty_env 0) t else t

let beta_eta_contract = eta_contract << beta_norm

(* eta-long beta-normal form *)

let rec eta_long Ts t =
    match t with
        | Abs (s, T, t) -> Abs (s, T, eta_long (T :: Ts) t)
        | _ ->
            match strip_comb t with
                | (Abs _, _) -> eta_long Ts (beta_norm t)
                | (u, ts) ->
                    let Us = binder_types (fastype_of1 (Ts, t))
                    let i = List.length Us
                    let long = eta_long (List.rev Us @ Ts)
                    Library.fold_rev 
                        (Term.abs << (fun p -> ("x", p))) 
                        Us
                        (list_comb (incr_boundvars i u, List.map (long << incr_boundvars i) ts @ List.map (long << Bound) [i - 1 .. -1 .. 0]))

let distinct_bounds t =
    let rec dis vars t =
        match t with 
            | App (u, v) -> let (vars, u') = dis vars u
                            let (vars, v') = dis vars v
                            (vars, App (u', v'))
            | Abs (s, T, b) -> let name = Library.singleton (Name.variant_list vars) s
                               let (vars, b') = dis (name :: vars) b
                               (vars, Abs (name, T, b'))
            | _ -> (vars, t)
    snd (dis [] t)
