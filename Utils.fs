module Utils

open Term

exception BadPosition of term * int list

(*let rec subterm_positions pos (t', t) =
  let ty = type_of t'
  match (t', t) with
    | (Abs (n, T, _), Abs (_, _, s)) ->
            let aa = (t', Free(n, T))
                        |> Term.betapply
//                        |> Envir.beta_eta_contract
            (t, ty, List.rev pos) :: subterm_positions (0 :: pos) (aa, s)
    | (App (p', q'), App (p, q)) ->
            (t, ty, List.rev pos) :: subterm_positions (0 :: pos) (p', p) @ subterm_positions (1 :: pos) (q', q)
    | _ -> [(t, ty, List.rev pos)]*)

let rec subterm_positions pos (t', t) =
  let ty = type_of t'
  match (t', t) with
    | (Abs (n, T, s'), Abs (_, _, s)) ->
            let aa = (snd << dest_abs) (n,T,s')
            (t', ty, List.rev pos) :: subterm_positions (0 :: pos) (aa, s)
    | (App (p', q'), App (p, q)) ->
            (t', ty, List.rev pos) :: subterm_positions (0 :: pos) (p', p) @ subterm_positions (1 :: pos) (q', q)
    | _ -> [(t', ty, List.rev pos)]

let positions t = 
    subterm_positions [] (t, t)

let rec bounds_at_position t pos =
    match (t, pos) with
         (Abs (n, ty, t), 0 :: is) -> (n, ty) :: bounds_at_position t is
        | (App (p, _), 0 :: is) -> bounds_at_position p is
        | (App (_, q), 1 :: is) -> bounds_at_position q is
        | (_, []) -> []
        | (t, pos) -> raise (BadPosition (t, pos))

let rec substitute (t', pos) t =
    match ((t', pos), t) with
        ((t', 0 :: pos), Abs (v, T, t)) -> Abs (v, T, substitute (t', pos) t)
      | ((t', 0 :: pos), App (p, q)) -> App (substitute (t', pos) p, q)
      | ((t', 1 :: pos), App (p, q)) -> App (p, substitute (t', pos) q)
      | ((t', []), _) -> t'
      | ((_, pos), t) -> raise (BadPosition (t, pos))
