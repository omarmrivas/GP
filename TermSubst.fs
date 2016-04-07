module TermSubst

open Term

let map_atypsT_same f =
    let rec typ T =
        match T with
            | Type (a, Ts) -> Type (a, Same.map typ Ts)
            | T -> f T
    typ
