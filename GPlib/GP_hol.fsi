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

type individual =
    {genome: Expr list
     norm: Expr
     fitness: float}

val get_gp_data :
            term_size       : int ->
            population_size : int ->
            generations     : int ->
            bests           : int ->
            mutation_prob   : float ->
            finish          : (float -> bool) ->
            timeOut         : int ->
            seed            : int ->
            scheme          : Expr
                           -> gp_data

val gp : data  : gp_data
              -> individual option
        