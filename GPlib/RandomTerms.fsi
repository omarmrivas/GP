module RandomTerms

open System
open Microsoft.FSharp.Quotations

type par_data = Random * (Type * (Type*bigint) list * int -> bigint)

(* Counting of terms *)
val count_term' : Type -> (Type * bigint) list -> int -> bigint
val count_terms  : Type -> int -> bigint

(* Random generation of terms *)
val random_term : par_data -> Type -> int -> Expr option