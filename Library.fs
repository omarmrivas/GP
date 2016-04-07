module Library

open System
open System.Threading
open System.Threading.Tasks
open Ops

let the_default x S =
    match S with
        | Some y -> y
        | None -> x

(*conditional application*)
let incogn b f = fun x -> if b then f x else x

(*List constructions*)
let cons = (fun x xs -> x :: xs)

(*Identity*)
let I x = x
let K x = fun _ -> x
let curry f x y = f (x, y)
let uncurry f (x, y) = f x y

let rec AList_lookup eq l key' =
        match l with
            [] -> None
          | ((key, value)::xs) ->
            if eq (key', key)
            then Some value
            else AList_lookup eq xs key'

//let rnd = ref (new System.Random())

(*let inline rndNext(i, j) =
    lock rnd (fun () -> (!rnd).Next(i, j))

let inline nextDouble() =
    lock rnd (fun () -> (!rnd).NextDouble())


let weightRnd (L : ('a * int) list) =
    let choosen = rndNext(0, List.sumBy (fun (_, w) -> w) L)
    let rec fld L i = 
        match L with
            | (x, w) :: L -> 
                let i = i + w
                if choosen < i then x
                else fld L i
            | _ -> failwith "Should not fail 51"
    fld L 0*)

let inline rndNext (rnd : System.Random) (i, j) =
    lock rnd (fun () -> rnd.Next(i, j))

let inline nextDouble (rnd : System.Random) =
    lock rnd (fun () -> rnd.NextDouble())

let weightRnd (rnd : System.Random) (L : ('a * int) list) =
    let choosen = rndNext rnd (0, List.sumBy (fun (_, w) -> w) L)
    let rec fld L i = 
        match L with
            | (x, w) :: L -> 
                let i = i + w
                if choosen < i then x
                else fld L i
            | _ -> failwith "Should not fail 51"
    fld L 0

(*the following versions of fold are designed to fit nicely with infixes*)

(*  (op @) (e, [x1, ..., xn])  ===>  ((e @ x1) @ x2) ... @ xn
    for operators that associate to the left (TAIL RECURSIVE)*)
let foldl (f: 'a * 'b -> 'a) : 'a * 'b list -> 'a =
  let rec itl arg =
        match arg with
        | (e, []) -> e
        | (e, a::l) -> itl (f(e, a), l)
  itl

(*  (op @) ([x1, ..., xn], e)  ===>   x1 @ (x2 ... @ (xn @ e))
    for operators that associate to the right (not tail recursive)*)
let foldr f (l, e) =
    let rec itr l =
        match l with
            | [] -> e
            | (a::l) -> f (a, itr l)
    itr l

let rec fold f l y =
  match l with
    | [] -> y
    | x :: xs -> fold f xs (f x y)

let rec fold_rev f l y =
  match l with
    | [] -> y
    | x :: xs -> f x (fold_rev f xs y)

let rec fold_map f l y =
  match l with
    | [] -> ([], y)
    | x :: xs ->
      let (x', y') = f x y
      let (xs', y'') = fold_map f xs y'
      (x' :: xs', y'')


(* basic list functions *)

let rec eq_list eq (list1, list2) =
  System.Object.ReferenceEquals (list1, list2) ||
    let rec eq_lst A =
        match A with
            | (x :: xs, y :: ys) -> eq (x, y) && eq_lst (xs, ys)
            | _ -> true
    List.length list1 = List.length list2 && eq_lst (list1, list2)

let rec maps f l =
  match l with
    | [] -> []
    | x :: xs -> f x @ maps f xs

let filter = List.filter
let filter_out f = filter (not << f)
let map_filter = List.choose

let rec take n xs =
  match (n,xs) with
    | (0: int,_) -> []
    | (_, []) -> []
    | (n, x :: xs) -> x :: take (n - 1) xs

let rec drop n xs =
  match (n,xs) with
    | (0: int, xs) -> xs
    | (_, []) -> []
    | (n, x :: xs) -> drop (n - 1) xs

let rec chop n xs =
  match (n, xs) with
    | (0: int, xs) -> ([], xs)
    | (_, []) -> ([], [])
    | (n, x :: xs) -> chop (n - 1) xs |>> cons x

let rec chop_groups n list =
  match chop (max n 1) list with
    | ([], _) -> []
    | (g, rest) -> g :: chop_groups n rest

(** lists **)

let rec remove_element i l =
    match i, l with
    | 0, x::xs -> xs
    | i, x::xs -> x::remove_element (i - 1) xs
    | i, [] -> failwith "index out of range"

let single x = [x]

let the_single L =
    match L with 
        | [x] -> x
        | _ -> failwith "List.Empty"

let singleton f x = the_single (f [x])

(** lists as sets -- see also Pure/General/ord_list.ML **)

(* canonical operations *)

let rec mmember eq list x =
  let rec memb l =
    match l with
        | [] -> false
        | y :: ys -> eq (x, y) || memb ys
  memb list

let insert eq x xs = if mmember eq xs x then xs else x :: xs
let remove eq x xs = if mmember eq xs x then filter_out (fun y -> eq (x, y)) xs else xs
let update eq x xs = cons x (remove eq x xs)

let inter eq xs = filter (mmember eq xs)

let union eq = fold (insert eq)
let subtract eq = fold (remove eq)

let merge eq (xs, ys) =
  if System.Object.ReferenceEquals(xs, ys) then xs
  else if List.isEmpty xs then ys
  else fold_rev (insert eq) ys xs

(*makes a list of the distinct members of the input; preserves order, takes
  first of equal elements*)
let distinct eq lst =
  let rec dist L =
    match L with
        | (rev_seen, []) -> List.rev rev_seen
        | (rev_seen, x :: xs) ->
          if mmember eq rev_seen x then dist (rev_seen, xs)
          else dist (x :: rev_seen, xs)
  dist ([], lst)


(*
    Combinatoric functions
*)
let next_digit Ln L =
    (List.zip L Ln)
    |> List.rev
    |> List.fold (fun (foo, L) (i, i_n) ->
                         if foo then 
                             if i + 1 < i_n 
                             then (false, (i + 1) :: L)
                             else (true, 0 :: L)
                         else (foo, i :: L)) (true, []) 
    |> (fun (foo, L) -> if foo then None
                        else Some L)

let lazy_one_of_each LL =
    let sizes = List.map List.length LL
    let foo = List.exists (fun n -> n = 0) sizes
    let state = [for i in 1 .. List.length LL - 1 -> 0]// (1 upto (length LL - 1))
                      |> (fun l -> l @ [-1])
    let rec one_of_each state = 
        seq {match next_digit sizes state with
                        Some state -> yield (List.map2 List.item state LL)
                                      yield! one_of_each state
                      | None -> ()}
    if foo then Seq.empty
    else one_of_each state

let binomialCoefficient n k =
    if k < 0 || k > n
    then 0
    else
      let k = if k > n - k 
              then n - k
              else k
      let n_k = n - k
      let c = 1
      [1 .. k]
            |> List.fold (fun c i -> c * (n_k + i) / i) c

let choose set k x =
    let rec maximize a b x =
                if (binomialCoefficient a b) <= x then a
                else maximize (a - 1) b x
    let rec iterate n x i =
                match i with
                | 0 -> []
                | i -> let max = maximize n i x
                       max :: iterate n (x - (binomialCoefficient max i)) (i - 1)
    if x < 0 then failwith "x < 0 !!!"
    else let idxs = iterate (List.length set) x k
         List.sort (List.map (fun i -> List.item i set) (List.sort idxs))

(*separate s [x1, x2, ..., xn]  ===>  [x1, s, x2, s, ..., s, xn]*)
let rec separate s L =
    match L with
        | x :: (_ :: _ as xs) -> x :: s :: separate s xs
        | xs -> xs

(* [x1, ..., xi, ..., xn]  --->  ([x1, ..., xi], [x(i+1), ..., xn])
   where xi is the last element that does not satisfy the predicate*)
let rec take_suffix pred L = 
    match L with
        | [] -> ([], [])
        | (x :: xs) ->
            match take_suffix pred xs with
                | ([], sffx) -> if pred x then ([], x :: sffx) else ([x], sffx)
                | (prfx, sffx) -> (x :: prfx, sffx)

let suffix (sffx : string) s = s + sffx

let unsuffix (sffx : string) (s : string) =
  if  s.EndsWith(sffx) then s.Substring(0, s.Length - sffx.Length)
  else failwith "unsuffix"


let rec is_prefix eq l1 l2 =
    match (l1, l2) with
        ([], _) -> true
      | (x :: xs, y :: ys) -> eq (x, y) && is_prefix eq xs ys
      | (_, _) -> false

let rec replicate_string n a =
    match n with
        | (0: int) -> ""
        | 1 -> a
        | k ->
            if k % 2 = 0 then replicate_string (k / 2) (a + a)
            else replicate_string (k / 2) (a + a) + a

let explode (s : string) = 
    s.ToCharArray() 
        |> Array.map string
        |> Array.toList

let implode L = String.concat "" L

(* pairs *)

let pair x y = (x, y)
let rpair x y = (y, x)

let fst (x, y) = x
let snd (x, y) = y

let eq_fst eq ((x1, _), (x2, _)) = eq (x1, x2)
let eq_snd eq ((_, y1), (_, y2)) = eq (y1, y2)
let eq_pair eqx eqy ((x1, y1), (x2, y2)) = eqx (x1, x2) && eqy (y1, y2)

let swap (x, y) = (y, x)

let apfst f (x, y) = (f x, y)
let apsnd f (x, y) = (x, f y)
let pairself f (x, y) = (f x, f y)


(*let timeout time def f v =
    let computation = async {return f v}
    try
        Async.RunSynchronously(computation, timeout = time)
    with //| :? System.TimeoutException -> def
         | e -> def

let withTimeout (timeout : TimeSpan) (computation : 'a Async) (*: 'a Async*) =
    let invokeOnce funcs =
        let counter = ref 0
        let invokeOnce' f x =
            if (System.Threading.Interlocked.CompareExchange (counter, 1, 0) = 0) then
                f x
        let (a, b, c) = funcs
        (invokeOnce' a, invokeOnce' b, invokeOnce' c)
    let callback (success, error, cancellation) =
        let (success, error, cancellation) = invokeOnce (success, error, cancellation)
        let fetchResult = async {
            let! result = computation
            success result }
        let timeoutExpired = async {
            do! Async.Sleep (int timeout.TotalMilliseconds)
            let ex = new TimeoutException ("Timeout expired") :> Exception
            error ex }
 
        Async.StartImmediate fetchResult
        Async.StartImmediate timeoutExpired
    callback |> Async.FromContinuations
             |> Async.RunSynchronously
//             |> Async.StartImmediate

let timeout2 time def f v =
    let computation = async {return f v}
    try
        withTimeout (TimeSpan.FromMilliseconds time) computation
        //Async.RunSynchronously(computation, timeout = time)
    with | :? System.TimeoutException -> def
         | e -> def*)

let timeout time def f v =
    try
        let tokenSource = new CancellationTokenSource()
        let token = tokenSource.Token
        let task = Task.Factory.StartNew(fun () -> f v, token)
        if not (task.Wait(time, token))
        then def
        else (fun (x, y) -> x) task.Result
    with e -> def

let serialize (file : string) obj =
    let serializer = System.Runtime.Serialization.Formatters.Binary.BinaryFormatter()
    let stream = new System.IO.FileStream(file, System.IO.FileMode.Create, System.IO.FileAccess.Write, System.IO.FileShare.None)
    serializer.Serialize(stream, obj)
    stream.Close()

let deserialize<'T> (file : string) =
    let serializer = System.Runtime.Serialization.Formatters.Binary.BinaryFormatter()
    let stream = new System.IO.FileStream(file, System.IO.FileMode.Open, System.IO.FileAccess.Read, System.IO.FileShare.Read)
    let obj = serializer.Deserialize(stream) :?> 'T
    stream.Close()
    obj
