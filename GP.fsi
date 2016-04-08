module GPhol

open Term
open Microsoft.FSharp.Quotations

type individual =
    {genome: term
     norm: term
     fit: float}

type result<'T> =
    individual * 'T

val evolve<'T>   : Expr list -> (term -> Expr<'T> -> 'T -> float) -> (float -> bool) -> int -> int -> int -> int -> float -> int -> result<'T> option