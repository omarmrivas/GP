module GPhol

open System
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Linq.QuotationEvaluation
//open System.Collections.Generic
open System.Collections.Concurrent
open Microsoft.FSharp.Collections
//open FSharp.Collections.ParallelSeq
open Term
open Ops

[<Serializable>]
type context = 
    {consts: Map<string, Reflection.MemberInfo>
     maxidx: int
     fresh_names: int
//     unknown_expr: Map<Expr, string>
     unknown_consts: Map<string, Expr>
     types: Map<string, Type>}

type gp_data<'T> =
    {function_set: Expr list
     func_set: term list
     term_size: int
     population_size: int
     bests: int
     target_typ: typ
     mutation_prob: float
     fitness: term -> Expr<'T> -> 'T -> float
     finish: float -> bool
     term_count: (int * int) list
     rnd : Random
     ctxt: context
     timeout : int}

type individual =
    {genome: term
     norm: term
     fit: float}

type result<'T> =
    individual * 'T

exception Done of individual

exception PartialApplication of term
exception UnknownExpression of Expr

let empty_context : context = 
    {consts = Map.empty
     maxidx = 0
     fresh_names = 0
//     unknown_expr = ConcurrentDictionary<Expr, string>();
     unknown_consts = Map.empty
     types = Map.empty}

let context_fold func ctxt arguments =
    arguments
        |> Array.fold (fun (ctxt, typs) typ -> 
                 let (ctxt, typ) = func ctxt typ
                 (ctxt, typ :: typs)) (ctxt, [])
        |> (fun (ctxt, typs) -> (ctxt, typs |> List.rev))

let rec fstype_to_holtype ctxt (fstyp : System.Type) =
    if Reflection.FSharpType.IsFunction fstyp
    then let (ty1, ty2) = Reflection.FSharpType.GetFunctionElements fstyp
         let (ctxt, ty1) = fstype_to_holtype ctxt ty1
         let (ctxt, ty2) = fstype_to_holtype ctxt ty2
         (ctxt, ty1 --> ty2)
    elif Reflection.FSharpType.IsTuple fstyp
    then let typs = Reflection.FSharpType.GetTupleElements fstyp
         typs |> context_fold fstype_to_holtype ctxt
              |> (fun (ctxt, typs) -> (ctxt, mk_prodTs typs))
    else match fstyp.Name with
         | "UInt16" -> (ctxt, TVar (("'a", 0), ["HOL.type"]))
         | "Int16" -> (ctxt, TVar (("'b", 0), ["HOL.type"]))
         | _ ->
             let arguments = fstyp.GetGenericArguments()
             let name = fstyp.Name
             let ctxt = {ctxt with types = Map.add name fstyp ctxt.types}
//             ignore (ctxt.types.TryAdd(name, fstyp))
             let (ctxt, typs) = context_fold fstype_to_holtype ctxt arguments
             (ctxt, Type (name, typs))

let rec holtype_to_fstype ctxt (typ : Term.typ) =
   match typ with
    | Type ("fun",[S;T]) ->
        (holtype_to_fstype ctxt S, holtype_to_fstype ctxt T)
            |> Reflection.FSharpType.MakeFunctionType
    | Type (name, args) -> 
            let args = args |> List.map (holtype_to_fstype ctxt)
                            |> List.toArray
//            let mutable fstype = typeof<int>
            if Map.containsKey name ctxt.types//ctxt.types.TryGetValue(name, &fstype)
            then let not_muted_fstype = Map.find name ctxt.types
                 try
                      let gtyp = not_muted_fstype.GetGenericTypeDefinition()
                      gtyp.MakeGenericType(args)
                 with | :? System.InvalidOperationException -> not_muted_fstype
            else System.Type.GetType(name)
    | TFree _ -> typedefof<_>
    | TVar _ -> typedefof<_>

let rec expr_to_holterm ctxt env expr =
    match expr with
        | Lambda (param, body) -> 
(*            let env = match param.Type.FullName with
                        | "System.Object" -> Map.add param.Name ctxt.maxidx env
                        | _ -> env*)
//            let (ctxt, body) = expr_to_holterm {ctxt with maxidx = ctxt.maxidx + 1} env body
            let (ctxt, body) = expr_to_holterm ctxt env body
            let (ctxt, T) = fstype_to_holtype ctxt param.Type
            (ctxt, Abs (param.Name, T, body))
        | Call (None, methodInfo, exprList) -> 
            let name = methodInfo.Name
            let ctxt = {ctxt with consts = Map.add name (methodInfo :> Reflection.MemberInfo) ctxt.consts}
//            ignore (ctxt.consts.TryAdd(name, methodInfo :> Reflection.MemberInfo))
            let (ctxt, typ) = fstype_to_holtype ctxt expr.Type
//            printfn "typs': %A" (expr.Type.GetGenericTypeDefinition())
            let (ctxt, typs) = exprList |> List.map (fun (ex : Expr) -> ex.Type)
                                        |> List.toArray
                                        |> context_fold fstype_to_holtype ctxt
//                        List.map (fstype_to_holtype << (fun (ex : Expr) -> ex.Type)) exprList
            exprList
                 |> List.fold (fun (indx, args) t -> let (indx, t) = expr_to_holterm ctxt env t
                                                     (indx, t :: args)) (ctxt, [])
                 |> (fun (ctxt, args) -> (ctxt, Term.list_comb (Const (methodInfo.Name, typs ---> typ), List.rev args)))
        | PropertyGet (None, methodInfo, []) as pg -> 
                    let name = methodInfo.Name
                    let ctxt = {ctxt with consts = Map.add name (methodInfo :> Reflection.MemberInfo) ctxt.consts}
//                    ignore (ctxt.consts.TryAdd(name, methodInfo :> Reflection.MemberInfo))
//                    let ctxt = {ctxt with consts = Map.add methodInfo.Name (methodInfo :> Reflection.MemberInfo) ctxt.consts}
                    let (ctxt, T) = fstype_to_holtype ctxt pg.Type
                    (ctxt, Const (methodInfo.Name, T))
        | Application (expr1, expr2) -> let (ctxt, e1) = expr_to_holterm ctxt env expr1
                                        let (ctxt, e2) = expr_to_holterm ctxt env expr2
                                        (ctxt, App (e1, e2))
        | Let (var, expr1, expr2) ->
            let (ctxt, e1) = expr_to_holterm ctxt env expr1
            let (ctxt, e2) = expr_to_holterm ctxt env expr2
            let (ctxt, T) = fstype_to_holtype ctxt var.Type
            (ctxt, App (Abs (var.Name, T, e2), e1))
        | IfThenElse (x, y, z) ->
            let (ctxt, x) = expr_to_holterm ctxt env x
            let xT = type_of x
            let (ctxt, y) = expr_to_holterm ctxt env y
            let yT = type_of y
            let (ctxt, z) = expr_to_holterm ctxt env z
            let zT = type_of z
            (ctxt, App (App (App (Const ("IfThenElse", xT --> (yT --> (zT --> zT))), x), y), z))
        | Microsoft.FSharp.Quotations.Patterns.Var var -> 
            let (ctxt, T) = fstype_to_holtype ctxt expr.Type
            (ctxt, Free (var.Name, T))
//        | Value (value, typ) -> (ctxt, Const (value.ToString(), fstype_to_holtype typ))
        | expr -> raise (UnknownExpression expr)
                  (*if ctxt.unknown_expr.ContainsKey(expr)
                  then let (ctxt, T) = fstype_to_holtype ctxt expr.Type
                       (ctxt, Const (ctxt.unknown_expr.[expr], T))
                  else let (ctxt, T) = fstype_to_holtype ctxt expr.Type
                       lock context_monitor (fun () ->
                            let name = "c" + string ctxt.fresh_names
                            ignore (ctxt.unknown_expr.TryAdd(expr, name))
                            ignore (ctxt.unknown_consts.TryAdd(name, expr))
                            ctxt.fresh_names <- ctxt.fresh_names + 1
                            (ctxt, Const (name, T)))*)

let expr_to_hol ctxt expr =
    expr |> expr_to_holterm ctxt Map.empty
         |> (fun (ctxt, t) -> 
                t |> (Envir.beta_eta_contract << RandomTerms.normalize_term)
                  |> (fun t -> (ctxt, t)))

let rec holterm_to_expr ctxt vars = function
   | Const (name, typ) -> 
        if ctxt.consts.ContainsKey(name)
        then
//            let mutable memberInfo = Unchecked.defaultof<Reflection.MemberInfo>
            if Map.containsKey name ctxt.consts//(ctxt.consts.TryGetValue(name, &memberInfo))
            then
                match Map.find name ctxt.consts with
                | :? Reflection.PropertyInfo as memberInfo -> 
                    Expr.PropertyGet (memberInfo, [])
                | :? Reflection.MethodInfo as memberInfo ->
                        match Expr.TryGetReflectedDefinition memberInfo with
                            | Some expr -> expr
                            | None -> let typs = Term.binder_types typ
                                      let vars =  [1 .. List.length typs]
                                                    |> List.map2 (fun T i -> ("y" + string i, T)) typs
                                                    |> List.map (fun (name, T) -> Microsoft.FSharp.Quotations.Var(name, holtype_to_fstype ctxt T))
                                      let head = Expr.Call (memberInfo, List.map Expr.Var vars)
                                      vars |> List.rev
                                           |> List.fold (fun t var -> Expr.Lambda (var, t)) head
                | _ -> failwith "Invalid Type!"
            else failwith ("Methdo not found: " + name)
        else //let mutable expr = <@@ 5 @@>
             if Map.containsKey name ctxt.unknown_consts//ctxt.unknown_consts.TryGetValue(name, &expr)
             then let expr = Map.find name ctxt.unknown_consts
                  let name expr = match expr with
                                    | Microsoft.FSharp.Quotations.Patterns.Var var -> var.Name
                                    | _ -> failwith (expr.ToString())
                  match expr with
                    | IfThenElse (x, y, z) -> Expr.IfThenElse (Expr.Var( Map.find (name x) vars ),
                                                               Expr.Var( Map.find (name y) vars ),
                                                               Expr.Var( Map.find (name z) vars ))
                    | _ -> expr
             else failwith ("Const not found: " + name)
   | Free (name, typ) -> Expr.Var( Map.find name vars )
   | Var ((name, _), typ) -> failwith "Invalid meta-variable"
   | App (s, t) -> 
        let (h, args) = strip_comb (App (s, t))
        match h with
            | Const ("IfThenElse", T) ->
                    let args = List.map (holterm_to_expr ctxt vars) args
                    match args with
                        | [x; y; z] -> Expr.IfThenElse (x, y, z)
                        | [x; y] -> let zT = y.Type
                                    let z = Microsoft.FSharp.Quotations.Var("z", zT)
                                    Expr.Lambda (z, Expr.IfThenElse (x, y, Expr.Var z))
                        | [x] -> let ty = type_of (App (s, t))
                                 let yzT = ty |> domain_type
                                              |> holtype_to_fstype ctxt
                                 let y = Microsoft.FSharp.Quotations.Var("y", yzT)
                                 let z = Microsoft.FSharp.Quotations.Var("z", yzT)
                                 Expr.Lambda (y, Expr.Lambda (z, Expr.IfThenElse (x, Expr.Var y, Expr.Var z)))
                        | _ -> raise (PartialApplication (App (s, t)))
            | _ -> Expr.Application (holterm_to_expr ctxt vars s, holterm_to_expr ctxt vars t)
   | Abs (name, T, t) as abst ->
            let v = Microsoft.FSharp.Quotations.Var(name, holtype_to_fstype ctxt T)
            let vars = Map.add name v vars
            let t' = (abst, Free(name, T)) |> Term.betapply
                                           |> Envir.beta_eta_contract
            Expr.Lambda (v, holterm_to_expr ctxt vars t')
   | X -> failwith "Invalid bound term"

let hol_to_expr ctxt t = 
    try 
        holterm_to_expr ctxt Map.empty t
    with | :? PartialApplication -> 
                printfn "Partial IfThenElse: %A" t
                raise (PartialApplication t)

let mk_individual lam norm fit : individual =
    {genome = lam
     norm = norm
     fit = fit}

let prepare (data : gp_data<'T>) lam =
    lam |> Library.rpair data.func_set
        |> (Envir.beta_eta_contract << list_comb)

let make_result<'T> (data : gp_data<'T>) (i : individual) =
    let expr = Expr.Cast<'T> (hol_to_expr data.ctxt i.norm)
    let func = try expr.Compile() ()
               with err -> printfn "Error expr: %A" expr
                           raise err
    (i, func)

let initial_population (data : gp_data<'T>) =
    let typ = List.map type_of data.func_set ---> data.target_typ
    let prep = prepare data
    let rec new_individual i (all, uniques, repeated) =
        let t = data.term_count |> Library.weightRnd data.rnd
                                |> RandomTerms.random_term data.rnd typ
                                |> Option.get
        let t' = prep t
        if i < data.population_size
        then if Set.contains t' all
             then new_individual (i+1) (all, uniques, repeated)
             else (Set.add t' all, t :: uniques, repeated)
        else (all, uniques, t :: repeated)
    let new_individual' ((all, uniques, repeated), _) =
        [1 .. Environment.ProcessorCount]
            |> PSeq.pick (fun _ -> Some (new_individual 0 (all, uniques, repeated)))
    [1 .. data.population_size]
        |> Library.pair (Set.empty, [], [])
        |> Library.foldl new_individual'
        |> (fun (_, uniques, repeated) -> 
                let uniques = uniques |> List.toArray
                                      |> Array.Parallel.map
                                          (fun t -> let t' = prep t
//                                                    printfn "Term: %A" (term_to_string t')
                                                    let expr = Expr.Cast<'T> (hol_to_expr data.ctxt t')
                                                    let func = try expr.Compile() ()
                                                               with err -> printfn "Error expr: %A" expr
                                                                           raise err
                                                    let fit = Library.timeout data.timeout 100000.0
                                                                              (data.fitness t' expr) func
                                                    let ind = mk_individual t t' fit
                                                    if data.finish fit
                                                    then raise (Done ind)
                                                    else ind)//(t, fit))
                                      |> Array.toList
                let all = Library.foldl (fun (all, ind) -> Map.add ind.norm ind all)
                                        (Map.empty, uniques)
                (all, uniques @ List.map (fun t -> let t' = prep t
                                                   let fit = (Map.find t' all).fit
                                                   mk_individual t t' fit) repeated))

(*Substitute new for free occurrences of old in a term*)
let subst pairs =
    match pairs with
        [] -> (fun x -> x)
      | pairs ->
        let rec substf i u =
            match Library.AList_lookup (fun (x,y) -> aconv x y) pairs u with
                Some (Bound j) -> Bound (i + j)
              | Some _ -> failwith "subst must map frees to bounds"
              | None -> (match u with 
                            Abs(a,T,t) -> Abs(a, T, substf (i+1) t)
                          | App (t,u') -> App (substf i t, substf i u')
                          | _ -> u)
        substf 0

let smaller (data : gp_data<'T>) s =
    let t = s
    let s = Envir.eta_long [] s
    let t = Envir.eta_long [] t
//    printfn "s: %A" (term_to_string s)
//    printfn "t: %A" (term_to_string t)
    let ps = Utils.positions s
    let qs = Utils.positions t
    let test dom cod =
          List.forall (fun (_, ty1) -> List.exists (fun (_, ty2) -> ty1 = ty2) cod) dom
    let count (_, _, p) =
        let qs' = qs |> List.map (fun (t_q, _, q) ->
                                let dom = Term.add_frees t_q []
                                let cod = Utils.bounds_at_position s p
                                let sigmas = 
                                    if Library.is_prefix (fun (x,y) -> x = y) p q
                                    then Some (dom |> List.map (fun (_, ty) ->
                                                                cod |> List.filter (fun (_, ty') -> ty = ty')
                                                                    |> List.length))
                                    else None
                                match sigmas with
                                    None -> 0
                                  | Some [] -> 1
                                  | Some sigmas -> Library.foldl (fun (x,y) -> x*y) (1, sigmas))
        Library.foldl (fun (x,y) -> x+y) (0, qs')
    let ps_weighted = ps |> List.map (fun (t, ty, pos) ->
                                        ((t, ty, pos), count (t, ty, pos)))
                         |> List.filter (fun (_, i) -> i > 0)
    let rec select ps_weighted =
        let (s_p, tao, p) = Library.weightRnd data.rnd ps_weighted
        let qs' = qs |> List.filter (fun (t_q, ty, q) ->
                                        let dom = Term.add_frees t_q []
                                        let cod = Utils.bounds_at_position s p
                                        ty = tao && test dom cod && Library.is_prefix (fun (x, y) -> x = y) p q)
        if List.isEmpty qs'
        then select (List.filter (fun x -> fst x <> (s_p, tao, p)) ps_weighted)
        else qs' |> List.map (fun x -> (x, 1))
                 |> Library.weightRnd data.rnd
                 |> Library.pair (s_p, tao, p)
    let ((_, _, p), (t_q, _, q)) = select ps_weighted
    let dom = Term.add_frees t_q []
    let cod = p |> Utils.bounds_at_position s
                |> List.rev
                |> List.mapi (fun i x -> (x, Bound i))
    let sigma = List.map (fun (s, ty) -> 
                            cod |> List.filter (fun ((_, ty'), _) -> ty = ty')
                                |> List.map (fun x -> (x, 1))
                                |> Library.weightRnd data.rnd
                                |> snd
                                |> Library.pair (Free (s, ty))) dom
(*    in (Utils.substitute (subst_atomic sigma t_q, p) s, p, q) end*)
    s |> Utils.substitute (subst sigma t_q, p)
      |> Envir.beta_eta_contract

let cross (data : gp_data<'T>) s t =
    let s = Envir.eta_long [] s
    let t = Envir.eta_long [] t
//    printfn "s: %A" (term_to_string s)
//    printfn "t: %A" (term_to_string t)
    let ps = Utils.positions s
    let qs = Utils.positions t
    let test dom cod =
          List.forall (fun (_, ty1) -> List.exists (fun (_, ty2) -> ty1 = ty2) cod) dom
    let count (_, _, p) =
        let qs' = qs |> List.map (fun (t_q, _, _) ->
                                let dom = Term.add_frees t_q []
                                let cod = Utils.bounds_at_position s p
                                let sigmas = dom |> List.map (fun (_, ty) ->
                                                                cod |> List.filter (fun (_, ty') -> ty = ty')
                                                                    |> List.length)
                                match sigmas with
                                    [] -> 1
                                  | _ :: _ -> Library.foldl (fun (x,y) -> x*y) (1, sigmas))
        Library.foldl (fun (x,y) -> x+y) (0, qs')
    let ps_weighted = ps |> List.map (fun (t, ty, pos) ->
                                        ((t, ty, pos), count (t, ty, pos)))
                         |> List.filter (fun (_, i) -> i > 0)
    let rec select ps_weighted =
        let (s_p, tao, p) = Library.weightRnd data.rnd ps_weighted
        let qs' = qs |> List.filter (fun (t_q, ty, _) ->
                                        let dom = Term.add_frees t_q []
                                        let cod = Utils.bounds_at_position s p
                                        ty = tao && test dom cod)
        if List.isEmpty qs'
        then select (List.filter (fun x -> fst x <> (s_p, tao, p)) ps_weighted)
        else qs' |> List.map (fun x -> (x, 1))
                 |> Library.weightRnd data.rnd
                 |> Library.pair (s_p, tao, p)
    let ((_, _, p), (t_q, _, q)) = select ps_weighted
    let dom = Term.add_frees t_q []
    let cod = p |> Utils.bounds_at_position s
                |> List.rev
                |> List.mapi (fun i x -> (x, Bound i))
    let sigma = List.map (fun (s, ty) -> 
                            cod |> List.filter (fun ((_, ty'), _) -> ty = ty')
                                |> List.map (fun x -> (x, 1))
                                |> Library.weightRnd data.rnd
                                |> snd
                                |> Library.pair (Free (s, ty))) dom
(*    in (Utils.substitute (subst_atomic sigma t_q, p) s, p, q) end*)
    (Utils.substitute (subst sigma t_q, p) s, p, q)

let crossover data s t =
    let (r, _, _) = cross data s t
    Envir.beta_eta_contract r
(*    let (r, p1, p2) = cross data s t
    printfn "p1: %A" p1
    printfn "p2: %A" p2
    let res = Envir.beta_eta_contract r
    printfn "res: %A" (term_to_string res)
    res*)

let mutation (data : gp_data<'T>) t =
   if data.rnd.NextDouble() < data.mutation_prob
   then
    let t = Envir.eta_long [] t
    let (_, ty, q) =
              t |> Utils.positions
                |> List.map (Library.rpair 1)
                |> Library.weightRnd data.rnd
    let bounds = q |> Utils.bounds_at_position t
                   |> List.rev
                   |> List.mapi (fun i x -> (x, Bound i))
    let target_typ = bounds |> List.map (snd << fst)
                            |> (fun typs -> typs ---> ty)
    let term_count = [|1 .. data.term_size|]
//                          |> Array.Parallel.map (fun i -> (i, RandomTerms.count_terms target_typ i))
                          |> Array.map (fun i -> (i, RandomTerms.count_terms target_typ i))
                          |> Array.toList
                          |> List.filter (fun (_, c) -> c > 0)
    let s = term_count |> Library.weightRnd data.rnd
                       |> RandomTerms.random_term data.rnd target_typ
                       |> Option.get
                       |> Library.rpair (List.map snd bounds)
                       |> (Envir.beta_eta_contract << list_comb)
    Utils.substitute (s, q) t
   else t

let next_generation (data : gp_data<'T>)
                    (all : Map<term,individual>,
                     pool : individual list) =
    let prep = prepare data
    let av_size =
            pool |> List.map (fun ind -> size_of_term ind.genome)
                 |> Library.pair 0
                 |> Library.foldl (fun (x,y) -> x+y)
                 |> (fun x -> float x / float data.population_size)
    let av_error =
            pool |> List.map (fun ind -> ind.fit)
                 |> Library.pair 0.0
                 |> Library.foldl (fun (x,y) -> x+y)
                 |> (fun x -> x / float data.population_size)
    let bst_individual =
            pool |> List.minBy (fun ind -> ind.fit)
    let bst_error = bst_individual.fit
    printfn "Average size: %A" av_size
    printfn "Average error: %A" av_error
    printfn "Best error: %A" bst_error
    printfn "Best Individual: %A" (term_to_string bst_individual.genome)
    printfn "Normal Form: %A" (term_to_string bst_individual.norm)
    let pool' = pool |> List.map (fun ind -> {ind with fit = 1.0 / ind.fit})
                     |> (fun pool -> let minv = List.minBy (fun ind -> ind.fit) pool
                                     List.map (fun ind -> let i = (ind.fit / minv.fit) |> System.Math.Round
                                                                                       |> int
                                                          (ind, i)) pool)
    let new_norm_genome _ =
        let i1 = Library.weightRnd data.rnd pool'
        let i2 = Library.weightRnd data.rnd pool'
        i2.genome |> crossover data i1.genome
                  |> mutation data
                  |> Envir.beta_eta_contract
                  |> (fun genome -> (prep genome, genome))
    let new_norm_genome_smaller _ =
        let i = Library.weightRnd data.rnd pool'
        i.genome
            |> smaller data
            |> (fun genome -> (prep genome, genome))
    let new_ind all (norm, t) =
        match Map.tryFind norm all with
            Some ind -> (norm, mk_individual t ind.norm ind.fit)
          | None -> 
(*                printfn "Lambda: %A" (term_to_string t)
                printfn "Lambda's type: %A" (type_of t)
                printfn "Norm: %A" (term_to_string norm)
                printfn "Norm's type: %A" (type_of norm)*)
                let expr = Expr.Cast<'T> (hol_to_expr data.ctxt norm)
                let func = try expr.Compile() ()
                           with err -> printfn "Error expr: %A" expr
                                       raise err
//                let fit = data.fitness norm expr func
                let fit = Library.timeout data.timeout 100000.0
                                          (data.fitness norm expr) func
                let ind = mk_individual t norm fit
                if data.finish fit
                then raise (Done ind)
                else (norm, ind)
    let rest = [|1 .. data.population_size - data.bests - data.bests|]
                   |> Array.map new_norm_genome
    let smaller = [|1 .. data.bests|]
                    |> Array.map new_norm_genome_smaller
//                   |> Array.Parallel.map new_norm_genome
    let rest_map = rest |> Array.append smaller
                        |> Map.ofArray
                        |> Map.toArray
                        |> Array.Parallel.map (new_ind all)
//                        |> Array.map (new_ind all)
                        |> Map.ofArray
    let rest_ind = rest |> Array.append smaller
                        |> Array.map (fun (norm, genome) -> 
                                let ind = Map.find norm rest_map
                                mk_individual genome norm ind.fit)
                        |> Array.toList
    let bests = Library.take data.bests pool
    let all = Map.fold (fun all norm ind -> Map.add norm ind all) all rest_map
    (all, bests @ rest_ind
            |> List.sortBy (fun ind -> ind.fit))

let evolve<'T> function_set (fitness : term -> Expr<'T> -> 'T -> float)
               finish term_size population_size generations bests mut_prob timeout : result<'T> option =
    printfn "Building initial population..."
    let ctxt = empty_context
    let (ctxt, target_typ) = fstype_to_holtype ctxt typeof<'T>
    let (ctxt, func_set) = 
        function_set
            |> tap (fun _ -> printfn "Arguments:")
            |> List.fold (fun (ctxt, func_set) (expr : Expr) ->
                printfn "Expr: %A, Type: %A" expr ((Term.typ_to_string << snd) (fstype_to_holtype ctxt expr.Type))
                let (ctxt, t) = expr_to_hol ctxt expr
                (ctxt, t :: func_set)) (ctxt, [])
            |> (fun (ctxt, func_set) -> (ctxt, List.rev func_set))
    let typ = List.map type_of func_set ---> target_typ
    let term_count = [| 1 .. term_size |]
                          |> Array.Parallel.map (fun i -> (i, RandomTerms.count_terms typ i))
                          |> Array.filter (fun (_, c) -> c > 0)
                          |> Array.toList
                          |> (fun L -> List.iter (printfn "%A") L
                                       L)
    let data : gp_data<'T> = 
        {function_set = function_set
         func_set = func_set
         term_size = term_size
         population_size = population_size
         bests = bests
         target_typ = target_typ
         mutation_prob = mut_prob
         fitness = fitness
         finish = finish
         term_count = term_count
         rnd = System.Random()
         ctxt = ctxt
         timeout = timeout}
    try
        let rec loop i all_pool : result<'T> option =
            printfn "Generation: %i" i
            if i < generations
            then loop (i + 1) (next_generation data all_pool)
            else None
        data |> initial_population
             |> loop 1
    with | :? System.AggregateException as ex
            -> let done_ex = ex.InnerException :?> Done
               //Some done_ex.Data0
               Some (make_result<'T> data done_ex.Data0)
         | Done ind -> //Some ind
                       Some (make_result<'T> data ind)
