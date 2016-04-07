module Term

open System
open Ops
open Library

(*Indexnames can be quickly renamed by adding an offset to the integer part,
  for resolution.*)
type indexname = string * int

(* Types are classified by sorts. *)
type clas = string
type sort  = clas list
type arity = string * sort list * sort

(* The sorts attached to TFrees and TVars specify the sort of that variable *)
type typ = Type  of string * typ list
         | TFree of string * sort
         | TVar  of indexname * sort

(*Terms.  Bound variables are indicated by depth number.
  Free variables, (scheme) variables and constants have names.
  An term is "closed" if every bound variable of level "lev"
  is enclosed by at least "lev" abstractions.

  It is possible to create meaningless terms containing loose bound vars
  or type mismatches.  But such terms are not allowed in rules. *)

[<Serializable>]
type term =
    Const of string * typ
  | Free  of string * typ
  | Var   of indexname * typ
  | Bound of int
  | Abs   of string*typ*term
  | App   of term*term


(* Pretty printing *)
let rec typ_to_string typ =
    match typ with
        | Type ("fun", [S;T]) -> "(" + typ_to_string S + "->" + typ_to_string T + ")"
        | Type (name, typs) -> let pars= typs |> List.map typ_to_string
                                              |> String.concat ", "
                               name + "[" + pars + "]"
        | TFree (name, _) -> name
        | TVar ((name, indx), _) -> name + string indx

(*Errors involving type mismatches*)
exception TYPE of string * typ list * term list

(*Errors errors involving terms*)
exception TERM of string * term list

(*Note variable naming conventions!
    a,b,c: string
    f,g,h: functions (including terms of function type)
    i,j,m,n: int
    t,u: term
    v,w: indexnames
    x,y: any
    A,B,C: term (denoting formulae)
    S,T,U: typ
*)


(** Types **)

(*dummies for type-inference etc.*)
let dummyS = [""]
let dummyT = Type ("dummy", [])

let no_dummyT typ =
  let rec check T =
      match T with
      | Type ("dummy", _) as T ->
          raise (TYPE ("Illegal occurrence of '_' dummy type", [T], []))
      | (Type (_, Ts)) -> List.iter check Ts
      | _ -> ()
  check typ
  typ

let (-->) S T = Type("fun",[S;T])

(*handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)*)
let (--->) = List.foldBack (-->)

let mk_prodT (T1, T2) = Type ("Product_Type.prod", [T1; T2])

let mk_prodTs ts = Type ("Product_Type.prod", ts)

let dest_Type T =
  match T with
    | Type (x,y) -> (x,y)
    | T -> raise (TYPE ("dest_Type", [T], []))
let dest_TVar T =
  match T with
    | TVar (x,y) -> (x,y)
    | T -> raise (TYPE ("dest_TVar", [T], []))
let dest_TFree T =
  match T with
    | TFree (x,y) -> (x,y)
    | T -> raise (TYPE ("dest_TFree", [T], []))

(** Discriminators **)

let is_Bound t =
  match t with
    | Bound _ -> true
    | _  -> false

let is_Const t =
  match t with
    | Const _ -> true
    | _ -> false

let is_Free t =
  match t with
  | Free _ -> true
  | _ -> false

let is_Var t =
  match t with
    | Var _ -> true
    | _ -> false

let is_TVar t =
  match t with
    | TVar _ -> true
    | _ -> false



(** Destructors **)

let dest_Const t =
  match t with
  | Const (x,y) -> (x,y)
  | t -> raise (TERM("dest_Const", [t]))

let dest_Free t =
  match t with
  | Free (x,y) -> (x,y)
  | t -> raise (TERM("dest_Free", [t]))

let dest_Var t =
  match t with
  | Var (x,y) -> (x,y)
  | t -> raise (TERM("dest_Var", [t]))

let dest_comb t =
  match t with
  | App (t1, t2) -> (t1, t2)
  | t -> raise (TERM("dest_comb", [t]))

let domain_type typ =
  match typ with
  | Type ("fun", [T; _]) -> T
  | _ -> raise (TYPE ("domain_type", [typ], []))

let range_type typ =
  match typ with
  | Type ("fun", [_; U]) -> U
  | _ -> raise (TYPE ("range_type", [typ], []))

let dest_funT typ =
  match typ with
  | Type ("fun", [T; U]) -> (T, U)
  | T -> raise (TYPE ("dest_funT", [T], []))


(* maps  [T1,...,Tn]--->T  to the list  [T1,T2,...,Tn]*)
let rec binder_types typ =
  match typ with
  | Type ("fun", [T; U]) -> T :: binder_types U
  | _ -> []

(* maps  [T1,...,Tn]--->T  to T*)
let rec body_type typ =
  match typ with
  | Type ("fun", [_; U]) -> body_type U
  | T -> T

(* maps  [T1,...,Tn]--->T  to   ([T1,T2,...,Tn], T)  *)
let strip_type T = (binder_types T, body_type T);


(*Compute the type of the term, checking that combinations are well-typed
  Ts = [T0,T1,...] holds types of bound variables 0, 1, ...*)
let rec type_of1 typ =
  match typ with
  | (Ts, Const (_,T)) -> T
  | (Ts, Free  (_,T)) -> T
  | (Ts, Bound i) -> try
                        List.item i Ts
                     with
                        | :? System.ArgumentException -> raise (TYPE("type_of: bound variable", [], [Bound i]))
  | (Ts, Var (_,T)) -> T
  | (Ts, Abs (_,T,body)) -> T --> type_of1(T::Ts, body)
  | (Ts, App (f, u)) ->
      let U = type_of1(Ts,u)
      let T = type_of1(Ts,f)
      match T with
           | Type("fun",[T1;T2]) ->
              if T1=U then T2 
              else raise (TYPE("type_of: type mismatch in application", [T1;U], [App (f, u)]))
           | _ -> raise (TYPE("type_of: function type is expected in application",[T;U], [App (f,u)]))


let type_of t : typ = type_of1 ([],t)


(*Determines the type of a term, with minimal checking*)
let rec fastype_of1 typ =
  match typ with
  | (Ts, App (f,u)) ->
    match fastype_of1 (Ts,f) with
        | Type("fun",[_;T]) -> T
        | _ -> raise (TERM("fastype_of: expected function type", [App (f,u)]))
  | (_, Const (_,T)) -> T
  | (_, Free (_,T)) -> T
  | (Ts, Bound i) -> try 
                        List.item i Ts
                     with
                        | :? System.ArgumentException -> raise (TERM("fastype_of: Bound", [Bound i]))
  | (_, Var (_,T)) -> T
  | (Ts, Abs (_,T,u)) -> T --> fastype_of1 (T::Ts, u)

let fastype_of t : typ = fastype_of1 ([],t)


(*Determine the argument type of a function*)
let argument_type_of tm k =
  let rec argT i T =
    match T with
        | (Type ("fun", [T; U])) -> if i = 0 then T else argT (i - 1) U
        | T -> raise (TYPE ("argument_type_of", [T], []))
  let rec arg i Ts t =
      match (i,t) with
        | (0,Abs (_, T, _)) -> T
        | (i, Abs (_, T, t)) -> arg (i - 1) (T :: Ts) t
        | (i, App (t,_)) -> arg (i + 1) Ts t
        | (i, a) -> argT i (fastype_of1 (Ts, a))
  arg k [] tm

let abs (x, T) t = Abs (x, T, t)

let rec strip_abs t =
  match t with
  | Abs (a, T, t) ->
      let (a', t') = strip_abs t
      ((a, T) :: a', t')
  | t -> ([], t)


(* maps  (x1,...,xn)t   to   t  *)
let rec strip_abs_body t =
  match t with
  | Abs(_,_,t) -> strip_abs_body t
  | u  ->  u


(* maps  (x1,...,xn)t   to   [x1, ..., xn]  *)
let rec strip_abs_vars t =
  match t with
  | Abs(a,T,t)  ->  (a,T) :: strip_abs_vars t
  | u  ->  [] : (string*typ) list


let strip_qnt_body qnt =
    let rec strip t =
        match t with
            | (App (Const(c,_),Abs(_,_,t)) as tm) -> if c=qnt then strip t else tm
            | t -> t
    strip

let strip_qnt_vars qnt =
    let rec strip t =
        match t with
            | App (Const(c,_),Abs(a,T,t)) -> if c=qnt then (a,T)::strip t else []
            | t  ->  [] : (string*typ) list
    strip


(* maps   (f, [t1,...,tn])  to  f(t1,...,tn) *)
let list_comb : term * term list -> term = foldl App


(* maps   f(t1,...,tn)  to  (f, [t1,...,tn]) ; naturally tail-recursive*)
let strip_comb u : term * term list =
    let rec stripc x =
        match x with
            | (App (f,t), ts) -> stripc (f, t::ts)
            | x -> x
    stripc(u,[])

(* maps   f(t1,...,tn)  to  f , which is never a combination *)
let rec head_of t =
  match t with
    | App (f,t) -> head_of f
    | u -> u

(*number of atoms and abstractions in a term*)
let rec size_of_term tm =
  let rec add_size t n =
    match t with
        | App (t, u) -> add_size t (add_size u n)
        | Abs (_ ,_, t) -> add_size t (n + 1)
        | _ -> n + 1
  add_size tm 0


(*number of atoms and constructors in a type*)
let size_of_typ ty =
  let rec add_size n T =
      match T with
      | Type (_, tys) -> List.fold add_size (n + 1) tys
      | _ -> n + 1
  add_size 0 ty


let rec map_atyps f T =
  match T with
  | Type (a, Ts) -> Type (a, List.map (map_atyps f) Ts)
  | T -> f T


let rec map_aterms f t =
  match t with
    | App (t, u) -> App (map_aterms f t, map_aterms f u)
    | Abs (a, T, t) -> Abs (a, T, map_aterms f t)
    | t -> f t

let map_type_tvar f = map_atyps (fun T -> match T with  | TVar (x,y) -> f (x,y) | T -> T)
let map_type_tfree f = map_atyps (fun T -> match T with | TFree (x,y) -> f (x,y) | T -> T)


let map_types f =
  let rec map_aux t =
    match t with
        | Const (a, T) -> Const (a, f T)
        | Free (a, T) -> Free (a, f T)
        | Var (v, T) -> Var (v, f T)
        | Bound i -> Bound i
        | Abs (a, T, t) -> Abs (a, f T, map_aux t)
        | App (t, u) -> App (map_aux t, map_aux u)
  map_aux

(* fold types and terms *)

let rec fold_atyps (f : typ -> 'a -> 'a) T =
  match T with
    | Type (_, Ts) -> fold (fold_atyps f) Ts
    | T -> f T


let fold_atyps_sorts f =
  fold_atyps (fun T -> 
    match T with 
        | TFree (_, S) -> f (T, S) 
        | TVar (_, S) -> f (T, S)
        | _ -> raise (TYPE ("fold_atyps_sorts", [T], [])))


let rec fold_aterms f t =
  match t with
    | App (t, u) -> (fold_aterms f t) %> (fold_aterms f u)
    | Abs (_, _, t) -> fold_aterms f t
    | a -> f a


let rec fold_term_types f t =
  match t with
    | Const (_, T) -> f t T
    | Free (_, T) -> f t T
    | Var (_, T) -> f t T
    | Bound _ -> I
    | Abs (_, T, b) -> f t T %> fold_term_types f b
    | App (t, u) -> fold_term_types f t %> fold_term_types f u


let fold_types f = fold_term_types (K f)


let rec replace_types t u =
  match (t,u) with
    | (Const (c, _), T :: Ts) -> (Const (c, T), Ts)
    | (Free (x, _), T :: Ts) -> (Free (x, T), Ts)
    | (Var (xi, _), T :: Ts) -> (Var (xi, T), Ts)
    | (Bound i, Ts) -> (Bound i, Ts)
    | (Abs (x, _, b), T :: Ts) ->
        let (b', Ts') = replace_types b Ts
        (Abs (x, T, b'), Ts')
    | (App (t, u), Ts) ->
        let (t', Ts') = replace_types t Ts
        let (u', Ts'') = replace_types u Ts'
        (App (t', u'), Ts'')
    | _ -> raise (TERM("replace_types", [t]))


let burrow_types f ts =
  let Ts = List.rev ((fold << fold_types) (fun x xs -> x :: xs) ts [])
  let Ts' = f Ts
  let (ts', X) = fold_map replace_types ts Ts'
  match X with
    | [] -> ()
    | _ -> raise (TERM("burrow_types", ts))
  ts'

(*collect variables*)
let add_tvar_namesT = fold_atyps (fun ty -> match ty with | TVar (xi, _) -> insert (fun (x, y) -> x = y) xi | _ -> I)
let add_tvar_names = fold_types add_tvar_namesT
let add_tvarsT = fold_atyps (fun ty -> match ty with | TVar (v,w) -> insert (fun (x, y) -> x = y) (v,w) | _ -> I)
let add_tvars = fold_types add_tvarsT
let add_var_names = fold_aterms (fun ty -> match ty with | Var (xi, _) -> insert (fun (x, y) -> x = y) xi | _ -> I)
let add_vars = fold_aterms (fun ty -> match ty with | Var (v,w) -> insert (fun (x, y) -> x = y) (v,w) | _ -> I)
let add_tfree_namesT = fold_atyps (fun ty -> match ty with | TFree (a, _) -> insert (fun (x, y) -> x = y) a | _ -> I)
let add_tfree_names = fold_types add_tfree_namesT
let add_tfreesT = fold_atyps (fun ty -> match ty with | TFree (v,w) -> insert (fun (x, y) -> x = y) (v,w) | _ -> I)
let add_tfrees = fold_types add_tfreesT
let add_free_names = fold_aterms (fun t -> match t with | Free (x, _) -> insert (fun (x, y) -> x = y) x | _ -> I)
let add_frees = fold_aterms (fun t -> match t with | Free (v,w) -> insert (fun (x, y) -> x = y) (v,w) | _ -> I)
let add_const_names = fold_aterms (fun t -> match t with | Const (c, _) -> insert (fun (x, y) -> x = y) c | _ -> I)
let add_consts = fold_aterms (fun t -> match t with | Const (c,ty) -> insert (fun (x, y) -> x = y) (c,ty) | _ -> I)


(*extra type variables in a term, not covered by its type*)
let hidden_polymorphism t =
  let T = fastype_of t
  let tvarsT = add_tvarsT T []
  let extra_tvars = 
    fold_types (fold_atyps
                    (fun ty -> match ty with 
                                | TVar (v,w) -> if mmember (fun (x, y) -> x = y) tvarsT (v,w) 
                                                then I 
                                                else insert (fun (x, y) -> x = y) (v,w ) 
                                | _ -> I)) t []
  extra_tvars



(** Comparing terms **)

(* variables *)

let eq_ix ((x, i): indexname, (y, j)) = i = j && x = y

let eq_tvar ((xi, S: sort), (xi', S')) = eq_ix (xi, xi') && S = S'
let eq_var ((xi, T: typ), (xi', T')) = eq_ix (xi, xi') && T = T'

(* alpha equivalence *)

let rec aconv tm1 tm2 =
  System.Object.ReferenceEquals (tm1, tm2) ||
  match (tm1, tm2) with
    | (App (t1, u1), App (t2, u2)) -> aconv t1 t2 && aconv u1 u2
    | (Abs (_, T1, t1), Abs (_, T2, t2)) -> aconv t1 t2 && T1 = T2
    | (a1, a2) -> a1 = a2


(* renaming variables *)


(*Abstraction of the term "body" over its occurrences of v,
    which must contain no loose bound variables.
  The resulting term is ready to become the body of an Abs.*)
let abstract_over (v, body) =
  let rec abs lev tm =
      if aconv v tm then Bound lev
      else
        match tm with
            | Abs (a, T, t) -> Abs (a, T, abs (lev + 1) t)
            | App (t, u) ->
                try
                    App (abs lev t, try abs lev u with Same.SAME -> u)
                with 
                    | Same.SAME -> App (t, abs lev u)
            | _ -> raise Same.SAME
  try abs 0 body with | Same.SAME -> body


let absfree (a, T) body = Abs (a, T, abstract_over (Free (a, T), body))

let rec has_abs t = 
  match t with
    | Abs _ -> true
    | App (t, u) -> has_abs t || has_abs u
    | _ -> false


(* loose_bvar(t,k) iff t contains a 'loose' bound variable referring to
   level k or beyond. *)
let rec loose_bvar t =
  match t with
    | (Bound i,k) -> i >= k
    | (App (f,t), k) -> loose_bvar(f,k) || loose_bvar(t,k)
    | (Abs(_,_,t),k) -> loose_bvar(t,k+1)
    | _ -> false

let rec loose_bvar1 t =
  match t with 
    | (Bound i,k) -> i = k
    | (App (f,t), k) -> loose_bvar1 (f,k) || loose_bvar1 (t,k)
    | (Abs(_,_,t),k) -> loose_bvar1 (t,k+1)
    | _ -> false

let is_open t = loose_bvar (t, 0)
let is_dependent t = loose_bvar1 (t, 0)

(*increments a term's non-local bound variables
  required when moving a term within abstractions
     inc is  increment for bound variables
     lev is  level at which a bound variable is considered 'loose'*)
let rec incr_bv (inc, lev, u) = 
  match u with
    | Bound i -> if i>=lev then Bound(i+inc) else u
    | Abs(a,T,body) -> Abs(a, T, incr_bv(inc,lev+1,body))
    | App (f,t) -> App (incr_bv(inc,lev,f), incr_bv(inc,lev,t))
    | _ -> u

let incr_boundvars inc t =
  match inc with
    | 0 -> t
    | inc -> incr_bv(inc,0,t)


(*Special case: one argument*)
let subst_bound (arg, t) : term =
  let rec subst (t, lev) =
    match (t,lev) with
        | (Bound i, lev) ->
          if i < lev then raise Same.SAME   (*var is locally bound*)
          else if i = lev then incr_boundvars lev arg
          else Bound (i - 1)   (*loose: change it*)
        | (Abs (a, T, body), lev) -> Abs (a, T, subst (body, lev + 1))
        | (App (f, t), lev) ->
            try 
                App (subst (f, lev), try subst (t, lev) with Same.SAME -> t)
            with Same.SAME -> App (f, subst (t, lev))
        | _ -> raise Same.SAME
  try subst (t, 0) with Same.SAME -> t

(*Replace the ATOMIC term ti by ui;    inst = [(t1,u1), ..., (tn,un)].
  A simultaneous substitution:  [ (a,b), (b,a) ] swaps a and b.  *)
let rec subst_atomic inst tm =
    match (inst, tm) with 
        ([], tm) -> tm
      | (inst, tm) ->
            let rec subst t =
                match t with
                    (Abs (a, T, body)) -> Abs (a, T, subst body)
                  | (App (t, u)) -> App (subst t, subst u)
                  | t -> Library.the_default t (Library.AList_lookup (fun (x, y) -> aconv x y) inst t)
            subst tm

(*beta-reduce if possible, else form application*)
let betapply = function
  | (Abs(_,_,t), u) -> subst_bound (u,t)
  | (f,u) -> App (f, u)

let betapplys = Library.foldl betapply

(* maximum index of typs and terms *)

let rec maxidx_typ T i = 
    match T with
        | TVar ((_, j), _) -> max i j
        | Type (_, Ts) -> maxidx_typs Ts i
        | TFree _ -> i
and maxidx_typs T i = 
    match T with
        | [] -> i
        | T :: Ts -> maxidx_typs Ts (maxidx_typ T i)

let rec maxidx_term t i = 
    match t with
        | Var ((_, j), T) -> maxidx_typ T (max i j)
        | Const (_, T) -> maxidx_typ T i
        | Free (_, T) -> maxidx_typ T i
        | Bound _ -> i
        | Abs (_, T, t) -> maxidx_term t (maxidx_typ T i)
        | App (t, u) -> maxidx_term u (maxidx_term t i)

let maxidx_of_typ T = maxidx_typ T -1
let maxidx_of_typs Ts = maxidx_typs Ts -1
let maxidx_of_term t = maxidx_term t -1

(** misc syntax operations **)

(* substructure *)

let exists_subtype P =
    let rec ex ty = P ty ||
                    match ty with
                        | Type (_, Ts) -> List.exists ex Ts
                        | _ -> false
    ex

let exists_type P =
    let rec ex t =
        match t with
            | Const (_, T) -> P T
            | Free (_, T) -> P T
            | Var (_, T) -> P T
            | Bound _ -> false
            | Abs (_, T, t) -> P T || ex t
            | App (t, u) -> ex t || ex u
    ex

let exists_subterm P =
    let rec ex tm = 
        P tm ||
        match tm with
            | App (t, u) -> ex t || ex u
            | Abs (_, _, t) -> ex t
            | _ -> false
    ex

let exists_Const P = exists_subterm (fun t -> match t with | Const (n,T) -> P (n,T) | _ -> false)

let rec dest_abs (x, T, body) =
  let rec name_clash t =
        match t with
            | (Free (y, _)) -> x = y
            | (App (t, u)) -> name_clash t || name_clash u
            | (Abs (_, _, t)) -> name_clash t
            | _ -> false
  if name_clash body then
      dest_abs (singleton (Name.variant_list [x]) x, T, body)    (*potentially slow*)
  else (x, subst_bound (Free (x, T), body))

// Unification part

type tyenv = Map<indexname, sort * typ>

let tvar_clash ixn S S' =
  raise (TYPE ("Type variable has two distinct sorts", [TVar (ixn, S); TVar (ixn, S')], []))

let lookup tye (ixn, S) =
  match Map.tryFind ixn tye with
    None -> None
  | Some (S', T) -> if S = S' then Some T else tvar_clash ixn S S'

(*occurs check*)
let occurs v tye =
  let rec occ T =
    match T with
      | (Type (_, Ts)) -> List.exists occ Ts
      | (TFree _) -> false
      | (TVar (w, S)) ->
          eq_ix (v, w) ||
          match lookup tye (w, S) with
            | None -> false
            | Some U -> occ U
  occ

(*chase variable assignments; if devar returns a type var then it must be unassigned*)
let rec devar tye T =
  match T with
    | TVar (indx,S) ->
      match lookup tye (indx,S) with
        | Some U -> devar tye U
        | None -> T
    | T -> T

let update_new (k, x) m =
  if Map.containsKey k m 
    then failwith "Duplicated key"
    else Map.add k x m

exception TUNIFY

(*purely structural unification*)
let rec raw_unify (ty1, ty2) tye =
  match (devar tye ty1, devar tye ty2) with
    | (TVar (v, S1) as T, TVar (w, S2)) ->
      if eq_ix (v, w) then
        if S1 = S2 then tye else tvar_clash v S1 S2
      else update_new (w, (S2, T)) tye
    | (TVar (v, S), T) ->
      if occurs v tye T then raise TUNIFY
      else update_new (v, (S, T)) tye
    | (T, TVar (v, S)) ->
      if occurs v tye T then raise TUNIFY
      else update_new (v, (S, T)) tye
    | (Type (a, Ts), Type (b, Us)) ->
      if a <> b then raise TUNIFY
      else raw_unifys (Ts, Us) tye
    | (T, U) -> if T = U then tye else raise TUNIFY
and raw_unifys (T,U) tye = 
  match (T,U) with 
    | (T :: Ts, U :: Us) -> raw_unifys (Ts, Us) (raw_unify (T, U) tye)
    | ([], []) -> tye
    | _ -> raise TUNIFY


(* matching *)

exception TYPE_MATCH

(*purely structural matching*)
let rec raw_match (V,T) subs =
  match (V,T) with
    | (TVar (v, S), T) ->
      match lookup subs (v, S) with
        | None -> if V = T then subs else update_new (v, (S, T)) subs
        | Some U -> if U = T then subs else raise TYPE_MATCH
    | (Type (a, Ts), Type (b, Us)) ->
      if a <> b then raise TYPE_MATCH
      else raw_matches (Ts, Us) subs
    | (TFree (x,x'), TFree (y,y')) ->
      if (x,x') = (y,y') then subs else raise TYPE_MATCH
    | _ -> raise TYPE_MATCH
and raw_matches (T,U) subs =
  match (T,U) with
    | (T :: Ts, U :: Us) -> raw_matches (Ts, Us) (raw_match (T, U) subs)
    | ([], []) -> subs
    | _ -> raise TYPE_MATCH

// Pretty printing
let rec term_to_string term = 
    match term with
        | Const (c, _) -> c
        | Free (f, _) -> f
        | Var (idx, _) -> string idx
        | Abs (s, T, _) -> "(λ" + s + ". " + term_to_string (betapply (term, Free (s, T))) + ")"
        | App (s, t) -> "(" + term_to_string s + " " + term_to_string t + ")"
        | _ -> failwith "Free bound!"

