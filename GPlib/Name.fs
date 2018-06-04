module Name

(* local functions *)

let the_default x S =
    match S with
        | Some y -> y
        | None -> x

let rec fold f l y =
  match l with
    | [] -> y
    | x :: xs -> fold f xs (f x y)

let rec fold_map f l y =
  match l with
    | [] -> ([], y)
    | x :: xs ->
      let (x', y') = f x y
      let (xs', y'') = fold_map f xs y'
      (x' :: xs', y'')

let suffix (sffx : string) s = s + sffx

let unsuffix (sffx : string) (s : string) =
  if  s.EndsWith(sffx) then s.Substring(0, s.Length - sffx.Length)
  else failwith "unsuffix"

(* [x1, ..., xi, ..., xn]  --->  ([x1, ..., xi], [x(i+1), ..., xn])
   where xi is the last element that does not satisfy the predicate*)
let rec take_suffix pred L = 
    match L with
        | [] -> ([], [])
        | (x :: xs) ->
            match take_suffix pred xs with
                | ([], sffx) -> if pred x then ([], x :: sffx) else ([x], sffx)
                | (prfx, sffx) -> (x :: prfx, sffx)

let explode (s : string) = 
    s.ToCharArray() 
        |> Array.map string
        |> Array.toList

let implode L = String.concat "" L

let apfst f (x, y) = (f x, y)

(*conditional application*)
let incogn b f = fun x -> if b then f x else x

let rec replicate_string n a =
    match n with
        | (0: int) -> ""
        | 1 -> a
        | k ->
            if k % 2 = 0 then replicate_string (k / 2) (a + a)
            else replicate_string (k / 2) (a + a) + a

let the_single L =
    match L with 
        | [x] -> x
        | _ -> failwith "List.Empty"

let singleton f x = the_single (f [x])

(** common defaults **)

let uu = "uu"
let uu_ = "uu_"
let aT = "'a"

(** special variable names **)

(* encoded bounds *)

(*names for numbered variables --
  preserves order wrt. int_ord vs. string_ord, avoids allocating new strings*)

(* internal names *)

let internal_ = suffix "_";
let dest_internal = unsuffix "_";

let skolem = suffix "__";
let dest_skolem = unsuffix "__";

let rec clean_index (x, i) =
    try
        clean_index (dest_internal x, i + 1)
    with _ -> (x, i)

let clean x = (fun (x, _) -> x) (clean_index (x, 0))

(** generating fresh names **)

(* context *)

type context =
  Context of Map<string, string option>    (*declared names with latest renaming*)

let declare x (Context tab) =
    let key = clean x
    if Map.containsKey key tab
    then Context tab
    else Context (Map.add key None tab)

let declare_renaming (x, x') (Context tab) =
  Context (Map.add (clean x) (Some (clean x')) tab)

let is_declared (Context tab) = (fun key -> Map.containsKey key tab)
let declared (Context tab) = (fun key -> Map.tryFind key tab)

let context = Context Map.empty |> fold declare [""; "'"]
let make_context used = fold declare used context

(* invent names *)

let is_char (s : string) = s.Length = 1
let is_ascii (s : string) = is_char s && int (s.Chars(0)) < 128

let is_ascii_letter (s : string) =
  is_char s &&
   ("A" <= s && s <= "Z" ||
    "a" <= s && s <= "z")

let is_ascii_digit (s : string) =
  is_char s && "0" <= s && s <= "9"

let is_ascii_hex (s : string) =
  is_char s &&
  ("0" <= s && s <= "9" ||
   "A" <= s && s <= "F" ||
   "a" <= s && s <= "f")

let is_ascii_quasi s =
    match s with
        | "_" -> true
        | "'" -> true
        | _ -> false

let is_ascii_blank =
  function
    | " " -> true | "\t" -> true | "\n" -> true | "\^K" -> true | "\f" -> true | "\^M" -> true
    | _ -> false

let is_ascii_control s = is_char s && (int (s.Chars(0))) < 32 && not (is_ascii_blank s)

type kind = Letter | Digit | Quasi | Blank | Other

let kind s =
  if is_ascii_letter s then Letter
  else if is_ascii_digit s then Digit
  else if is_ascii_quasi s then Quasi
  else if is_ascii_blank s then Blank
  else if is_char s then Other
//  else if is_letter_symbol s then Letter
  else Other;

let is_letter s = kind s = Letter
let is_digit s = kind s = Digit
let is_quasi s = kind s = Quasi
let is_blank s = kind s = Blank

let is_symbolic (s : string) =
  s.StartsWith("\\<") && s.EndsWith(">") && not (s.StartsWith("\\<^"))

let rec symbolic_end L =
    match L with
        | (_ :: "\⇩" :: _) -> true
        | (_ :: "\\<^isub>" :: _) -> true  (*legacy*)
        | (_ :: "\\<^isup>" :: _) -> true  (*legacy*)
        | ("'" :: ss) -> symbolic_end ss
        | (s :: _) -> is_symbolic s
        | [] -> false

let bump_init str =
  if symbolic_end (List.rev (explode str)) then str + "'"
  else str + "a"

let bump_string str =
  let rec bump L =
    match L with
        | [] -> ["a"]
        | ("z" :: ss) -> "a" :: bump ss
        | (s :: ss) ->
          if is_char s && "a" <= s && s < "z"
          then (string (char (int (s.Chars(0)) + 1))) :: ss
          else "a" :: s :: ss

  let (ss, qs) = apfst List.rev (take_suffix is_quasi (explode str))
  let ss' = if symbolic_end ss then "'" :: ss else bump ss
  implode (List.rev ss' @ qs)

let invent ctxt =
  let rec invs x n =
    match (x, n) with
        | (_, 0) -> []
        | (x, n) ->
          let x' = bump_string x
          if is_declared ctxt x then invs x' n else x :: invs x' (n - 1)
  invs << clean

let invent_names ctxt x xs = List.map2 (fun x y -> (x,y)) (invent ctxt x (List.length xs)) xs

let invent_list = invent << make_context

(* variants *)

(*makes a variant of a name distinct from already used names in a
  context; preserves a suffix of underscores "_"*)
let variant name ctxt =
  let rec vary x =
      match declared ctxt x with
        | None -> x
        | Some x' -> vary (bump_string (the_default x x'))
  let (x, n) = clean_index (name, 0);
  let (x', ctxt') =
      if not (is_declared ctxt x) then (x, declare x ctxt)
      else
        let x0 = bump_init x
        let x' = vary x0
        let foo = (x0.CompareTo(x')) <> 0
        let ctxt' = 
                ctxt |> incogn foo (declare_renaming (x0, x'))
                     |> declare x'
        (x', ctxt')
  (x' + replicate_string n "_", ctxt')

let variant_list used names = (fun (x, y) -> x) (make_context used |> fold_map variant names)

let get_fresh_name names name = singleton (variant_list names) name