module Graph

open System
open DataTypes

[<Serializable>]
type PlanarGraph =
         {vertices: Vertex list
          edges : Edge list
          quadrilaterals: Quadrilateral list
          crossing_number: int
         }

let empty_graph = {vertices = []
                   edges = []
                   quadrilaterals = []
                   crossing_number = 0}

let is_collinear ((x, y) : Vertex) ((x1, y1) : Vertex, (x2, y2) : Vertex) =
    let numerator = y2 - y1
    let denominator = x2 - x1
    if denominator = zero then
         x = x1
    else let m = numerator / denominator
         let y' = m * (x - x1) + y1
         y = y'

let binomialCoefficient n k =
    if k < 0 || k > n
    then 0
    else
      let k = if k > n - k
              then n - k
              else k
      let n_k = n - k
      List.fold (fun c i -> c * (n_k + i) / i) 1 [1 .. k]

let choose set k x =
    let rec maximize a b x =
                if (binomialCoefficient a b) <= x then a
                else maximize (a - 1) b x
    let rec iterate n x i = 
                match i with
                | 0 -> []
                | i -> let max = maximize n i x
                       max :: iterate n (x - (binomialCoefficient max i)) (i - 1)
    if x < 0 then failwith "x < 0 !!!"
    else let idxs = iterate (List.length set) x k
         List.sort (List.map (fun indx -> List.item indx set) (List.sort idxs))

let cross_product2D ((vx, vy) : Vertex, (wx, wy) : Vertex) = vx * wy - vy * wx

let minus_vector2D ((vx, vy) : Vertex, (wx, wy) : Vertex) = (wx - vx, wy - vy) : Vertex

let edges_intersect (edge1 : Edge, edge2 : Edge) =
    let p = fst edge1
    let q = fst edge2
    let r = minus_vector2D edge1
    let s = minus_vector2D edge2
    let q_minus_p = minus_vector2D (p, q)
    let r_cross_s = cross_product2D (r, s)
    if r_cross_s = zero //parallel edges
    then false
    else let t = (cross_product2D (q_minus_p, s)) / r_cross_s
         if t <= zero || one <= t
         then false
         else let u = (cross_product2D (q_minus_p, r)) / r_cross_s
              if u <= zero || one <= u
              then false
              else true

let intersect_quadrilateral ((v1, v2, v3, v4) : Quadrilateral) =
    List.exists edges_intersect [((v1, v2), (v3, v4)); ((v1, v3), (v2, v4)); ((v1, v4), (v2, v3))]

let add_vertex graph vertex =
    match graph with
        None -> None
      | Some {vertices = vertices
              edges = edges
              quadrilaterals = quadrilaterals
              crossing_number = crossing_number} ->
          if List.exists (is_collinear vertex) edges then None
          else if List.length vertices < 3 then
            let vertices = vertex :: vertices
            let size = List.length vertices
            let edges = [0 .. (binomialCoefficient size 2 - 1)]
                          |> List.map (choose vertices 2)
                          |> List.map (function
                                        | [v1; v2] -> (v1, v2)
                                        | _ -> failwith "Impossible to raise this exception")
            {vertices = vertices
             edges = edges
             quadrilaterals = quadrilaterals
             crossing_number = crossing_number}
              |> Some
          else
            let size = List.length vertices
            let vertices' = vertex :: vertices
            let new_quadrilaterals = [0 .. (binomialCoefficient size 3 - 1)]
                                      |> List.map ((fun three -> List.sort (vertex :: three)) << (choose vertices 3))
                                      |> List.map (function
                                                      | [v1; v2; v3; v4] -> (v1, v2, v3, v4)
                                                      | _ -> failwith "Impossible to raise this exception")
            let crossing_number' = new_quadrilaterals |> List.toArray
                                                      |> Array.sumBy
                                                          (fun quad -> if intersect_quadrilateral quad
                                                                       then 1
                                                                       else 0)
            //printfn "crossing_number'"
            {vertices = vertices'; edges = List.map (fun v' -> (vertex,v')) vertices @ edges;
             quadrilaterals = quadrilaterals @ new_quadrilaterals;
             crossing_number = crossing_number + crossing_number'}
                  |> Some
