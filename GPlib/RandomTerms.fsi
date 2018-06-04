module RandomTerms

open System
open Microsoft.FSharp.Quotations

(* Counting of terms *)
val count_terms : Type -> int -> bigint

(* Random generation of terms *)
val random_term : Random -> Type -> int -> Expr option