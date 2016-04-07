module Ops

(*application and structured results*)
let (|->) (x, y) f = f x y
let (|>>) (x, y) f = (f x, y)
let (||>) (x, y) f = (x, f y)
let (||>>) (x, y) f = let (z, y') = f y
                      ((x, z), y')

let tap f x = ignore (f x)
              x

(*composition and structured results*)
let (%>) f g x   = x |> f |> g
let (%->) f g x  = x |> f |-> g
let (%>>) f  g x = x |> f |>> g
let (%%>) f g x  = x |> f ||> g
let (%%>>) f g x = x |> f ||>> g
