module Logic

open Term

let rec combound (t, n, k) =
    if  k>0 then App (combound (t,n+1,k-1), Bound n) else t

let incr_tvar_same n =
    match n with
        | 0 -> Same.same
        | k -> TermSubst.map_atypsT_same
                (fun typ -> match typ with 
                            | TVar ((a, i), S) -> TVar ((a, i + k), S)
                            | _ -> raise Same.SAME)


let incr_tvar k T = try incr_tvar_same k T with Same.SAME -> T

(*For all variables in the term, increment indexnames and lift over the Us
    result is ?Gidx(B.(lev+n-1),...,B.lev) where lev is abstraction level *)
let incr_indexes_same (Ts, k) =
    match (Ts, k) with
        | ([], 0) -> Same.same
        | (Ts, k) ->
            let n = List.length Ts
            let incrT = incr_tvar_same k
            let rec incr lev T =
                match T with
                    | Var ((x, i), T) ->
                        combound (Var ((x, i + k), Ts ---> Same.commit incrT T), lev, n)
                    | Abs (x, T, body) ->
                        try Abs (x, incrT T, try incr (lev + 1) body with Same.SAME -> body)
                        with Same.SAME -> Abs (x, T, incr (lev + 1) body)
                    | App (t, u) ->
                        try App (incr lev t, try incr lev u with Same.SAME -> u)
                        with Same.SAME -> App (t, incr lev u)
                    | Const (c, T) -> Const (c, incrT T)
                    | Free (x, T) -> Free (x, incrT T)
                    | Bound _ -> raise Same.SAME
            incr 0

let incr_indexes arg t = try incr_indexes_same arg t with Same.SAME -> t
