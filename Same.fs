module Same

exception SAME

type ffunction<'a, 'b> = 'a -> 'b
type operation<'a> = ffunction<'a, 'a>

let same _ = raise SAME
let commit f x = try f x with SAME -> x

let capture f x = try Some (f x) with SAME -> None

let ffunction f x =
  match f x with
    | None -> raise SAME
    | Some y -> y

let rec map f L =
  match L with
    | [] -> raise SAME
    | x :: xs -> try f x :: commit (map f) xs with SAME -> x :: map f xs

let map_option f V =
  match V with
    | None -> raise SAME
    | Some x -> Some (f x)

