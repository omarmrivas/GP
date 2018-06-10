module GP_hol

open System
open FSharp.Quotations.Evaluator
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns
open Utils

type par_data = Random * (Type * (Type*bigint) list * int -> bigint)

type gp_data =
    {scheme : Expr
     vars : Var list
     term_size: int
     population_size: int
     generations : int
     bests: int
     mutation_prob: float
     finish: float -> bool
     term_count: (int * bigint) [] list
     timeout : int
     par_data : par_data []}

type proto_individual =
    {genome: Expr list
     norm: Expr
     fitness: unit -> float}

type individual =
    {genome: Expr list
     norm: Expr
     fitness: float}

let memoize fn =
//  let cache = new System.Collections.Concurrent.ConcurrentDictionary<_,_>()
  let cache = new System.Collections.Generic.Dictionary<_,_>()
  (fun x ->
    match cache.TryGetValue x with
    | true, v -> v
    | false, _ -> let v = fn (x)
                  cache.[x] <- v
                  v)

let get_gp_data term_size population_size generations bests mutation_prob finish timeOut seed scheme =
    let tcount (var:Var) = 
            [| 1 .. term_size |]
                |> Array.map (fun i -> (i, RandomTerms.count_terms var.Type i))
                |> Array.filter (fun (_, c) -> c > bigint.Zero)
                |> (fun L -> printfn "Var: %A, counts: %A" var.Name L
                             L)
    let par_data = [| 1 .. population_size |]
                        |> Array.map (fun i -> (System.Random(i + seed), memoize (fun (A,env,s) -> RandomTerms.count_term' A env s)))
    let vars = lambdas scheme
    {scheme = scheme
     vars = vars
     term_size = term_size
     generations = generations
     population_size = population_size
     bests = bests
     mutation_prob = mutation_prob
     finish = finish
     term_count = List.map tcount vars
     timeout = timeOut
     par_data = par_data}

let mk_proto_individual (data : gp_data) lams : proto_individual =
    let norm = Expr.Applications(data.scheme, List.map List.singleton lams)
                |> expand Map.empty
    {genome = lams
    // needs beta-eta contraction
     norm = norm
     fitness = timeout data.timeout (fun () -> 0.0) (fun () -> norm.EvaluateUntyped() :?> (unit -> float)) ()}

let mk_individual (proto : proto_individual) : individual =
    {genome = proto.genome
    // needs beta-eta contraction
     norm = proto.norm
     fitness = proto.fitness ()}

(*let mk_individual (data : gp_data) lams : individual =
    let norm = Expr.Applications(data.scheme, List.map List.singleton lams)
                |> expand Map.empty
    {genome = lams
    // needs beta-eta contraction
     norm = norm
     fitness = timeout data.timeout 0.0 (fun () -> norm.EvaluateUntyped() :?> float) ()}*)

let initial_population (data : gp_data) =
    data.par_data
        |> pmap (fun (rnd,count_term) ->
                data.vars |> List.map2 (fun count var -> (count, var)) data.term_count
                          |> tap (fun _ -> printfn "Starting...")
                          |> List.choose (fun (count, var : Var) -> 
                            count |> weightRnd_bigint rnd
                                  |> RandomTerms.random_term (rnd,count_term) var.Type)
                          |> tap (fun _ -> printfn "Done"))
        |> pmap (mk_proto_individual data)
        |> pmap mk_individual

let mutation ((rnd,count_term) : par_data) (data : gp_data) t =
    let (_, ty, q) =
              t |> positions
                |> List.map (fun p -> (p,1))
                |> List.toArray
                |> weightRnd_int rnd
    let bounds = q |> bounds_at_position t
                   |> List.rev
    let target_typ = bounds |> List.map (fun var -> var.Type)
                            |> (fun typs -> typs ---> ty)
    let term_count = [|1 .. data.term_size|]
                        |> Array.map (fun i -> (i, RandomTerms.count_terms target_typ i))
                        |> Array.filter (fun (_, c) -> c > bigint.Zero)
    let s = term_count |> weightRnd_bigint rnd
                       |> RandomTerms.random_term (rnd,count_term) target_typ
                       |> Option.get
                       |> (fun lam -> Expr.Applications(lam, List.map (List.singleton << Expr.Var) bounds))
    t |> substitute (s, q)
      |> expand Map.empty

let Mutation ((rnd,count_term) : par_data) (data : gp_data) i =
    if rnd.NextDouble() < data.mutation_prob
    then let (prefix, x, suffix) = select_one rnd (rnd.Next (List.length i)) i
         prefix @ (mutation (rnd,count_term) data x :: suffix)
    else i

let crossover (rnd : System.Random) (data : gp_data) s t =
    let ps = positions s
    let qs = positions t
    let valid_cross_points (_, (tao:System.Type), p) =
        let cod = bounds_at_position s p
        qs |> List.filter (fun (_, (tao':System.Type), _) -> tao.ToString() = tao'.ToString())
           |> List.choose (fun (t_q, _, _) -> 
                    let dom = frees t_q
                    match dom with
                        [] -> Some ((t_q, []), 1)
                       | _ -> dom |> List.map (fun v -> (v, List.filter (fun (v':Var) -> v.Type.ToString() = v'.Type.ToString()) cod))
                                  |> List.map (fun (v, vs) -> ((v, vs), List.length vs))
                                  |> (fun xs -> let count = List.fold (fun c (_,s) -> c*s) 1 xs
                                                if count > 0
                                                then xs |> List.map fst
                                                        |> (fun xs -> Some ((t_q, xs), count))
                                                else None))
           |> (fun xs -> if List.isEmpty xs
                         then None
                         else Some ((p, xs), List.sumBy snd xs))
    ps |> List.choose valid_cross_points
       |> List.toArray
       // choose a p
       |> weightRnd_int rnd
       |> (fun (p, xs) -> (p, xs |> List.toArray
                                 |> weightRnd_int rnd))//choose a q
       |> (fun (p, (t_q, xs)) -> (p, (t_q, List.map (fun (v, vs) -> (v, vs |> List.map (fun v' -> (v',1))
                                                                           |> List.toArray
                                                                           |> weightRnd_int rnd
                                                                           |> Expr.Var)) xs))) // choose a sigma
       |> (fun (p, (t_q, sigma)) -> substitute (subst sigma t_q, p) s)
       |> expand Map.empty

let Crossover (rnd : System.Random) data i i' =
    let indx = rnd.Next (List.length i)
    let (prefix, s, suffix) = select_one rnd indx i
    let (_, t, _) = select_one rnd indx i'
    let x = crossover rnd data s t
    prefix @ (x :: suffix)

let gp (data : gp_data) : individual option =
    let rest_size = data.population_size - data.bests
    let next_generation data pool =
        let pool = Array.sortBy (fun i -> -i.fitness) pool
        let bests = Array.take data.bests pool
        let pool' = Array.map (fun i -> (i, i.fitness)) pool
        let rest = data.par_data
                        |> Array.take rest_size
                        |> Array.Parallel.map (fun (rnd,count_term) ->
                                let i1 = weightRnd_double rnd pool'
                                let i2 = weightRnd_double rnd pool'
                                let i = i2.genome |> Crossover rnd data i1.genome
                                                  |> Mutation (rnd,count_term) data
                                i)
                        |> Array.Parallel.map (mk_proto_individual data)
                        |> Array.Parallel.map mk_individual
        Array.append bests rest
    let rec loop i pool =
        printfn "Generation: %i" i
        match Array.tryFind (fun i -> data.finish i.fitness) pool with
            | Some i -> Some i
            | None -> if i < data.generations
                      then loop (i + 1) (next_generation data pool)
                      else None
    printfn "Building initial population..."
    data |> initial_population
         |> loop 1
