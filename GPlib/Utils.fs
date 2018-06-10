module Utils

open System
open System.Threading
open System.Threading.Tasks
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open RandomBigInteger

(* Generic utilities *)

let tap f x = f x |> ignore
              x

let pmap f xs =
    xs |> Array.chunkBySize 12
       |> Array.map (Array.Parallel.map f)
       |> Array.concat

// Not really useful as it would lead to stack overflows in
// non-terminating function calls
let timeout time def f v =
    try
        let tokenSource = new CancellationTokenSource()
        let token = tokenSource.Token
        let task = Task.Factory.StartNew(fun () -> f v, token)
        if not (task.Wait(time, token))
        then def
        else (fun (x, y) -> x) task.Result
    with e -> def

(* canonical operations *)

let rec mmember eq list x =
    let rec memb l =
        match l with
        | [] -> false
        | y :: ys -> eq (x, y) || memb ys
    memb list

let insert eq xs x = if mmember eq xs x then xs else x :: xs
let remove eq xs x = if mmember eq xs x then List.filter (fun y -> (not << eq) (x, y)) xs else xs

let inter eq xs = List.filter (mmember eq xs)
let union eq = List.fold (insert eq)
let subtract eq = List.fold (remove eq)

(* Combinatoric functions *)

let next_digit Ln L =
    (List.zip L Ln)
    |> List.rev
    |> List.fold (fun (foo, L) (i, i_n) ->
                         if foo then 
                             if i + 1 < i_n 
                             then (false, (i + 1) :: L)
                             else (true, 0 :: L)
                         else (foo, i :: L)) (true, []) 
    |> (fun (foo, L) -> if foo then None
                        else Some L)

(*let weightRnd_double (rnd : Random) (L : ('a * double) []) =
    let choosen = rnd.NextDouble() * Array.sumBy (fun (_, w) -> w) L
    let rec fld indx (L : ('a * double) []) i =
        let (x, w) = L.[indx]
        let i = i + w
        if choosen < i then x
        else fld (indx + 1) L i
    fld 0 L 0.0*)

let weightRnd_double (rnd : Random) (L : ('a * double) []) =
    let choosen = rnd.NextDouble() * Array.sumBy (fun (_, w) -> w) L
    let rec fld indx (L : ('a * double) []) i =
        if indx < Array.length L
        then let (x, w) = L.[indx]
             let i = i + w
             if choosen < i then x
             else fld (indx + 1) L i
        else fst L.[0]
    fld 0 L 0.0

let weightRnd_int (rnd : Random) (L : ('a * int) []) =
    let choosen = rnd.Next (Array.sumBy (fun (_, w) -> w) L)
    let rec fld indx (L : ('a * int) []) i =
        let (x, w) = L.[indx]
        let i = i + w
        if choosen < i then x
        else fld (indx + 1) L i
    fld 0 L 0

let weightRnd_bigint (rnd : Random) (L : ('a * bigint) []) =
//    let choosen = NextBigInteger rnd (bigint.Zero, Array.sumBy (fun (_, w) -> w) L)
    let choosen = RandomIntegerBelow rnd (Array.sumBy (fun (_, w) -> w) L)

    let rec fld indx (L : ('a * bigint) []) i =
        let (x, w) = L.[indx]
        let i = i + w
        if choosen < i then x
        else fld (indx + 1) L i
    fld 0 L bigint.Zero

let select_one (rnd : Random) i l =
    let prefix = List.take i l
    let suffix = List.skip i l
    (prefix, List.head suffix, List.tail suffix)


(* Functions on types *)

let (-->) S T = Reflection.FSharpType.MakeFunctionType (S,T)

(*handy for multiple args: [T1,...,Tn]--->T  gives  T1-->(T2--> ... -->T)*)
let (--->) : System.Type list -> System.Type -> System.Type = List.foldBack (-->)

let strip_type (fstyp : System.Type) =
    let rec strip typ =
        if Reflection.FSharpType.IsFunction typ
        then let (ty1, ty2) = Reflection.FSharpType.GetFunctionElements typ
             ty1 :: strip ty2
        else [typ]
    fstyp |> strip
          |> (fun typs -> (List.take (List.length typs - 1) typs, List.last typs))

let domain_type : System.Type -> System.Type = 
        fst << Reflection.FSharpType.GetFunctionElements
let range_type : System.Type -> System.Type = 
        snd << Reflection.FSharpType.GetFunctionElements

(* Quotations *)

let rec var_lookup l (key':Var) =
    match l with
        [] -> None
      | ((key:Var, value)::xs) ->
                if key'.Equals(key)
                then Some value
                else var_lookup xs key'

// Substitute new for free occurrences of old in a term
let subst pairs (s:Expr) =
    s.Substitute (var_lookup pairs)

let clone_expr t =
    let rec clone pairs s =
        match s with
        | Lambda (v, s) -> let v' = Var (v.Name, v.Type)
                           Expr.Lambda (v', clone ((v, Expr.Var v') :: pairs) s)
        | Application (p, q) -> Expr.Application (clone pairs p, clone pairs q)
        | Var v -> Option.get (var_lookup pairs v)
        | _ -> s
    clone [] t

// Beta-Let normalization
// Thanks to Tomas Petricek
let rec expand vars expr = 
  // First recursively process & replace variables
  let expanded = 
    match expr with
    // If the variable has an assignment, then replace it with the expression
    | ExprShape.ShapeVar v when Map.containsKey v vars -> vars.[v]
    // Apply 'expand' recursively on all sub-expressions
    | ExprShape.ShapeVar v -> Expr.Var v
    | Patterns.Call(body, DerivedPatterns.MethodWithReflectedDefinition meth, args) ->
        let this = match body with Some b -> Expr.Application(meth, b) | _ -> meth
        let res = Expr.Applications(this, [ for a in args -> [a]])
        expand vars res
    | ExprShape.ShapeLambda(v, expr) -> 
        Expr.Lambda(v, expand vars expr)
    | ExprShape.ShapeCombination(o, exprs) ->
        ExprShape.RebuildShapeCombination(o, List.map (expand vars) exprs)
  // After expanding, try reducing the expression - we can replace 'let'
  // expressions and applications where the first argument is lambda
  match expanded with
  | Patterns.Application(ExprShape.ShapeLambda(v, body), assign)
  | Patterns.Let(v, assign, body) ->
      expand (Map.add v (expand vars assign) vars) body
  | _ -> expanded

let rec lambdas expr =
    match expr with
        Lambda (param, body) -> 
            param :: lambdas body
      | _ -> []

exception BadPosition of Expr * int list

let rec subterm_positions pos = function
    | Lambda (_, s) as t -> (t, t.Type, List.rev pos) :: subterm_positions (0 :: pos) s
    | Application (p, q) as t -> (t, t.Type, List.rev pos) :: subterm_positions (0 :: pos) p @
                                                              subterm_positions (1 :: pos) q
    | t -> [(t, t.Type, List.rev pos)]

let positions t = subterm_positions [] t

let rec bounds_at_position t pos =
    match (t, pos) with
          (Lambda (var, t), 0 :: is) -> var :: bounds_at_position t is
        | (Application (p, _), 0 :: is) -> bounds_at_position p is
        | (Application (_, q), 1 :: is) -> bounds_at_position q is
        | (_, []) -> []
        | (t, pos) -> raise (BadPosition (t, pos))

let rec substitute (t', pos) t =
    match (pos, t) with
        (0 :: pos, Lambda (var, t)) -> Expr.Lambda (var, substitute (t', pos) t)
      | (0 :: pos, Application (p, q)) -> Expr.Application (substitute (t', pos) p, q)
      | (1 :: pos, Application (p, q)) -> Expr.Application (p, substitute (t', pos) q)
      | ([], _) -> t'
      | (pos, t) -> raise (BadPosition (t, pos))

let rec apply_at (f, pos) t =
    match (pos, t) with
        (0 :: pos, Lambda (var, t)) -> Expr.Lambda (var, apply_at (f, pos) t)
      | (0 :: pos, Application (p, q)) -> Expr.Application (apply_at (f, pos) p, q)
      | (1 :: pos, Application (p, q)) -> Expr.Application (p, apply_at (f, pos) q)
      | ([], t) -> f t
      | (pos, t) -> raise (BadPosition (t, pos))

let rec bounds t =
    let rec vars = function
        | Lambda (v, s) -> v :: bounds s
        | Application (p, q) as t -> bounds p @ bounds q
        | Var v -> [v]
        | _ -> []
    List.distinct (vars t)
//    List.distinctBy (fun (v : Var) -> v.Name) (vars t)

let rec vars_of_expr t =
    let rec vars = function
        | Lambda (v, s) -> vars_of_expr s
        | Application (p, q) as t -> vars_of_expr p @ vars_of_expr q
        | Var v -> [v]
        | _ -> []
    List.distinct (vars t)
//    List.distinctBy (fun (v : Var) -> v.Name) (vars t)

let frees t =
    subtract (fun (x:Var,y:Var) -> x.Equals(y)) (vars_of_expr t) (bounds t)

let rec get_letrecursive = function
    | Lambda (_, s) -> get_letrecursive s
    | Let(_, _, s) -> get_letrecursive s
    | LetRecursive (defs, _) -> List.map fst defs
    | _ -> []

let latex_tree (levelsep:float) (nodesep:float) t =
    let rec latext = function
        | Application (s, t) -> "\\pstree{\\TR{\\bullet}}{" +
                                (latext s) + (latext t) + "}"
        | Lambda (x, s) ->  "\\pstree{\\TR{\\lambda " +
                            x.Name + "}}{" + (latext s) + "}"
        | Var v -> "\\TR{Var\\ " + v.Name + "}"
        | Call(exprOpt, methodInfo, exprs) ->
            "\\pstree{\\TR{Call\\ " + (match exprOpt with
                                        Some expr -> expr.ToString()
                                      | None -> methodInfo.Name) + "}}{" +
            String.concat " " (List.map latext exprs) + "}"
        | PropertyGet(a, propOrValInfo, c) -> "\\TR{PropertyGet\\ " + propOrValInfo.Name + "}"
        | Let(var, expr1, expr2) -> "\\pstree{\\TR{let\\ " + var.Name + "}}{" +
                                    (latext expr1) + (latext expr2) + "}"
        | Value(value, typ) -> "\\TR{Value\\ " + value.ToString() + "}"
        | ValueWithName (v,T,name) -> "\\TR{ValueWithName\\ " + name + "=" + v.ToString() + "}"
        | IfThenElse (expr, s, t) -> "\\pstree{\\TR{if}}{" +
                                     (latext expr) + (latext s)  + (latext t) + "}"
        | LetRecursive (defs, expr) -> let aux ((v:Var),expr) = "\\pstree{\\TR{" + v.Name + "}}{" +
                                                                (latext expr) + "}"
                                       "\\pstree{\\TR{let\\ rec}}{" +
                                       String.concat " " (List.map aux defs) + latext expr + "}"
        | NewArray (T, exprs) -> "\\pstree{\\TR{array}}{" +
                                 String.concat " " (List.map latext exprs) + "}"
        | t -> "\\TR{" + t.ToString() + "}"
    "\\psset{levelsep=" + string levelsep + ",nodesep=" + string nodesep + "pt}" +
    latext t

let closure (max_calls : int) scheme =
    let names = scheme |> vars_of_expr
                       |> List.map (fun (v:Var) -> v.Name)
                       |> List.distinct
    let funcs = get_letrecursive scheme
    let (names, counters) = List.fold (fun (names, counters) (f:Var) -> 
                                    let name = Name.get_fresh_name names ("a" + f.Name)
                                    (name :: names, Var (name, typeof<int>) :: counters)) (names,[]) funcs
                            |> (fun (names, counters) -> (names, List.rev counters))
    let tao = List.map (fun (v:Var) -> (v, <@@ max_calls @@>)) counters
    let default_typs = funcs |> List.map (fun (v:Var) -> v.Type)
                             |> List.map (snd << strip_type)
    let defaults = List.map Expr.DefaultValue default_typs
    let count_typs = List.map (fun _ -> typeof<int>) funcs
    let (numargs, newtyps) = 
            funcs |> List.map (fun (v:Var) -> v.Type)
                  |> List.map strip_type
                  |> List.map (fun (args, ty) -> (List.length args, (count_typs @ args) ---> ty))
                  |> List.unzip
    let num_args_counters_defaults = List.zip3 numargs counters defaults
    let newfuncs = List.map2 (fun (v:Var) ty -> Var (v.Name, ty)) funcs newtyps
    let sigma = List.map2 (fun v v' -> (v, v')) funcs newfuncs
    let sigma' = List.map (fun (v, v') -> 
                    (v, Expr.Applications(Expr.Var v', 
                                          List.map (List.singleton << Expr.Var) counters))) sigma
    let prefix_lambdas vars expr = List.foldBack (fun v expr -> Expr.Lambda (v, expr)) vars expr
    let terminate_call c v expr = Expr.IfThenElse (<@@ (%%c:int) <= 0 @@>, v, expr)
    let dec c = <@@ (%%c : int) - 1 @@>
    let rec mk_closure = function
        | Lambda (v, s) -> Expr.Lambda (v, mk_closure s)
        | Let(v, s, t) -> Expr.Let(v, s, mk_closure t)
        | LetRecursive (defs, expr) -> 
            Expr.LetRecursive (List.map3 (fun (f,expr) (_, f') (n,c,d) -> 
                                    let sigma'' = [(c, dec (Expr.Var c))]
                                    let expr' = expr |> subst sigma'
                                                     |> apply_at (terminate_call (Expr.Var c) d << subst sigma'',
                                                                  [for i in 1..n do yield 0])
                                                     |> prefix_lambdas counters
                                    (f', expr')) defs sigma num_args_counters_defaults,
                               expr |> subst sigma'
                                    |> subst tao)
        | _ -> failwith "Unknown error on closure"
    mk_closure scheme
