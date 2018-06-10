module Utils

open System
open System.Threading
open System.Threading.Tasks
open Microsoft.FSharp.Quotations
open Microsoft.FSharp.Quotations.Patterns

(* Generic utilities *)

val tap : ('a -> 'b) -> 'a -> 'a
val pmap : ('a -> 'b) -> 'a [] -> 'b []

//val memoize : ('a -> 'b) -> ('a -> 'b)

// Not really useful as it would lead to stack overflows in
// non-terminating function calls
val timeout : int -> 'a -> ('b -> 'a) -> 'b -> 'a

(* canonical operations *)
val subtract : ('a*'b -> bool) -> ('b list -> 'a list -> 'b list)

(* Combinatoric functions *)
val next_digit       : int list -> int list -> int list option
val weightRnd_double : Random -> ('a*double)[] -> 'a
val weightRnd_int    : Random -> ('a*int)[] -> 'a
val weightRnd_bigint : Random -> ('a*bigint)[] -> 'a
val select_one       : Random -> int -> 'a list -> ('a list * 'a * 'a list)

(* Functions on types *)
val (-->)       : Type -> Type -> Type
val (--->)      : (Type list -> Type -> Type)
val strip_type  : Type -> Type list * System.Type
val domain_type : (Type -> Type)
val range_type  : (Type -> Type)

(* Quotations *)
val clone_expr         : Expr -> Expr
val lambdas            : Expr -> Var list
val get_letrecursive   : Expr -> Var list
val expand             : Map<Var,Expr> -> Expr -> Expr
val positions          : Expr -> (Expr * Type * int list) list
val bounds_at_position : Expr -> int list -> Var list
val substitute         : Expr * int list -> Expr -> Expr
val frees              : Expr -> Var list
val subst              : (Var * Expr) list -> Expr -> Expr
val latex_tree         : float -> float -> Expr -> string

val closure            : int -> Expr -> Expr