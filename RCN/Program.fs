// Learn more about F# at http://fsharp.org
// See the 'F# Tutorial' project for more help.

open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns
open Microsoft.FSharp.Quotations.DerivedPatterns

open DataTypes
open Graph
open Algebra

let lower_bound =
    [4, 0
     5, 1
     6, 3
     7, 9
     8, 19
     9, 36
     10, 62
     11, 102
     12, 153
     13, 229
     14, 324
     15, 447
     16, 603
     17, 798
     18, 1029
     19, 1318
     20, 1657
     21, 2055
     22, 2528
     23, 3077
     24, 3699
     25, 4430
     26, 5250
     27, 6180
     28, 7233
     29, 8421
     30, 9726]

let fitness f = 
        List.sumBy (fun (n, cn) -> 
                        match f n with
                            Some g -> let cn' = g.crossing_number
                                      let wc = List.length g.quadrilaterals
                                      let x = double (wc - cn')
                                      x * x
                          | None -> 0.0) lower_bound

let best_fitness =
    List.sumBy (fun (n, cn) -> let wc = binomialCoefficient n 4
                               let x = double (wc - cn)
                               x * x) lower_bound

// Original scheme
let scheme =
    <@@ fun Mx My Mz Gx Gy ->
         let rec x n : vector3D = 
                       if n <= 0
                       then V (one, zero, zero)
                       else Mx (n-1) zero one two three
                               div mul sin cos sinh cosh log exp
                               mk_vector3D mk_matrix
                               v_add v_sub dot cross v_norm
                               identity m_add m_sub multiplyM multiplyV translate scale rotate hrotate transpose det x y z
         and y n : vector3D = 
                       if n <= 0
                       then V (zero, one, zero)
                       else My (n-1) zero one two three
                               div mul sin cos sinh cosh log exp
                               mk_vector3D mk_matrix
                               v_add v_sub dot cross v_norm 
                               identity m_add m_sub multiplyM multiplyV translate scale rotate hrotate transpose det x y z
         and z n : vector3D =
                       if n <= 0
                       then V (zero, zero, one)
                       else Mz (n-1) zero one two three
                               div mul sin cos sinh cosh log exp
                               mk_vector3D mk_matrix
                               v_add v_sub dot cross v_norm
                               identity m_add m_sub multiplyM multiplyV translate scale rotate hrotate transpose det x y z
         and graph n = 
                [1 .. n]
                    |> List.map (fun i -> let xi = x i
                                          let yi = y i
                                          let zi = z i
                                          let cx = Gx zero one two three
                                                      div mul sin cos sinh cosh log exp
                                                      mk_vector3D mk_matrix
                                                      v_add v_sub dot cross v_norm
                                                      identity m_add m_sub multiplyM multiplyV translate scale rotate hrotate transpose det xi yi zi
                                          let cy = Gy zero one two three
                                                      div mul sin cos sinh cosh log exp
                                                      mk_vector3D mk_matrix
                                                      v_add v_sub dot cross v_norm
                                                      identity m_add m_sub multiplyM multiplyV translate scale rotate hrotate transpose det xi yi zi
                                          (cx, cy) : Vertex)
                    |> List.fold add_vertex (Some empty_graph)
         fun () -> fitness graph @@>

[<EntryPoint>]
let main argv =
(*    let t = RandomTerms.random_term (System.Random()) typeof<int->int->int> 3
    printfn "%A" t*)
    let closure = Utils.closure 31 scheme
    let term_size = 44
    let population_size = 200
    let generations = 1000
    let bests = 10
    let mutation_prob = 0.25
    let finish fit = best_fitness = fit
    let timeOut = 60000 // 1 minute
    let seed = System.DateTime().Millisecond
    let data = GP_hol.get_gp_data term_size population_size generations bests mutation_prob finish timeOut seed closure
    match GP_hol.gp data with
        | Some i -> printfn "Solution: %A" i
        | None -> printfn "oops"
    0 // return an integer exit code
    