type slice = string * int * int

type loc = At of { file : string; line : Z.t; col : Z.t } | NoLoc | Unknown
type name = Src of string | Gen of Z.t * string
type raw = Atom of loc * name | Wild of loc | Nat of loc * Z.t | Char of loc * int | Str of loc * string | List of loc * raw list

(* Each extern type one level deep, in the order and arities of its model's constructors: [_view] takes a host
   value apart into the constructor at the top and host values below, [_of] puts one together. *)
type 'v nat = Zero | Succ of 'v
type 'v half = HZ | H1 of 'v | H2 of 'v
type 'v str = SNil | SCons of 'v * 'v
type 'v rope = REmpty | RStr of 'v | RCat of 'v * 'v | RChar of 'v
type cmp = CLt | CEq | CGt
type dec = Yes | No

let () = if Sys.int_size <> 63 || not (Obj.is_int (Obj.repr (Z.of_int max_int))) then failwith "this runtime needs 63-bit ints, and zarith holding every value below 2^62 unboxed"

let nat_view ~z ~nat v = let n = z v in if Z.equal n Z.zero then Zero else Succ (nat (Z.pred n))
let nat_of ~z ~nat = function Zero -> nat Z.zero | Succ p -> nat (Z.succ (z p))

(* A number halved: H1 m is 2m+1, H2 m is 2m+2, so every positive integer has one view. *)
let half_view ~z ~nat v =
  let n = z v in
  if Z.equal n Z.zero then HZ else let m = nat (Z.shift_right (Z.pred n) 1) in if Z.is_odd n then H1 m else H2 m
let half_of ~z ~nat = function HZ -> nat Z.zero | H1 m -> nat (Z.succ (Z.shift_left (z m) 1)) | H2 m -> nat (Z.add (Z.shift_left (z m) 1) (Z.of_int 2))

(* A cons list of Char held as a slice of a byte string: the tail is a slice over the same buffer. *)
let str_view ~slice ~u8 ~str v = let s, o, l = slice v in if l = 0 then SNil else SCons (u8 (Z.of_int (Char.code (String.unsafe_get s o))), str (s, o + 1, l - 1))
let str_of ~z ~slice ~str = function
  | SNil -> str ("", 0, 0)
  | SCons (c, rest) -> let s, o, l = slice rest in str (String.make 1 (Char.chr (Z.to_int (z c))) ^ String.sub s o l, 0, l + 1)

(* The source spelling a printed literal reads back from (lib/literal.ml), shared with extracted programs: a
   character bare where the reader's word syntax admits it, hexadecimal otherwise, and a string escaped the way
   the reader unescapes. A Nat spells as Z.to_string. *)
(* An application's rendering (ASSUMPTIONS 184): a last argument that is itself an application keeps its own parens
   off and is written with `$` (DESIGN 2), so a right spine ends in no pile of them. Nothing else a value prints as
   opens with `(` -- a numeral, a character, a string, `_` and a constructor name all do not -- so the test names an
   application. One definition serves the interpreter, an extracted program and slc's output, as lit_char does. *)
let show_app name args =
  let rec go = function
    | [ s ] when String.length s > 1 && s.[0] = '(' -> [ "$ " ^ String.sub s 1 (String.length s - 2) ]
    | s :: rest -> s :: go rest
    | [] -> []
  in
  "(" ^ String.concat " " (name :: go args) ^ ")"

let lit_char c =
  if c = 32 then "#\\space"
  else if c = 10 then "#\\newline"
  else if c = 9 then "#\\tab"
  else if c >= 0x21 && c <= 0x7e && not (String.contains "();" (Char.chr c)) then Printf.sprintf "#\\%c" (Char.chr c)
  else Printf.sprintf "#\\x%02x" c

let lit_string s =
  let buf = Buffer.create (String.length s + 2) in
  Buffer.add_char buf '"';
  String.iter (fun c -> Buffer.add_string buf (match c with '"' -> "\\\"" | '\\' -> "\\\\" | '\n' -> "\\n" | '\t' -> "\\t" | ' ' .. '~' -> String.make 1 c | c -> Printf.sprintf "\\x%02x" (Char.code c))) s;
  Buffer.add_char buf '"';
  Buffer.contents buf

let add = Z.add
let sub = Z.sub
let mul = Z.mul
let div = Z.div
let divmod = Z.div_rem
let order c = if c < 0 then CLt else if c = 0 then CEq else CGt
let nat_cmp a b = order (Z.compare a b)
let decide b = if b then Yes else No
let lt_dec a b = decide (Z.lt a b)
let nat_mod = Z.rem
let nat_halve n = n
let shl n k = Z.shift_left n (Z.to_int k)
let nat_and = Z.logand
let nat_or = Z.logor
let nat_xor = Z.logxor
let shr n k = if Z.fits_int k then Z.shift_right n (Z.to_int k) else Z.zero
let small (a : Z.t) : int = Obj.magic a
let u62 f a b : Z.t = Obj.magic (f (small a) (small b) : int)
let u62_add = u62 ( + )
let u62_sub = u62 ( - )
let u62_mul = u62 ( * )
let u62_div = u62 ( / )
let u62_mod = u62 ( mod )
let u62_shl = u62 ( lsl )
let u62_shr = u62 ( lsr )
let u62_and = u62 ( land )
let u62_or = u62 ( lor )
let u62_xor = u62 ( lxor )
let u62_inc a : Z.t = Obj.magic (small a + 1 : int)
let u62_dec a : Z.t = Obj.magic (small a - 1 : int)
let u62_divmod a b = (u62_div a b, u62_mod a b)
let u62_cmp a b = order (compare (small a) (small b))
let u62_lt_dec a b = decide (small a < small b)
let trim (s, o, l) = (String.sub s o l, 0, l)
let str_cmp (s1, o1, l1) (s2, o2, l2) =
  let n = min l1 l2 in
  let rec go i =
    if i = n then if l1 < l2 then CLt else if l1 = l2 then CEq else CGt
    else if String.unsafe_get s1 (o1 + i) < String.unsafe_get s2 (o2 + i) then CLt
    else if String.unsafe_get s1 (o1 + i) > String.unsafe_get s2 (o2 + i) then CGt
    else go (i + 1)
  in
  go 0
let str_length (_, _, l) = Z.of_int l
let str_split (s, o, l) k = let k = Z.to_int k in ((s, o, k), (s, o + k, l - k))
let nat_str n = let s = Z.to_string n in (s, 0, String.length s)
let append (s1, o1, l1) (s2, o2, l2) = (String.sub s1 o1 l1 ^ String.sub s2 o2 l2, 0, l1 + l2)

(* A rope flattened in two passes: its leaves in order, then one buffer of their total length. [rope] views a
   node, [slice] and [z] read the two kinds of leaf, [str] makes the result. *)
let flatten ~rope ~slice ~z ~str root =
  let rec leaves acc = function
    | [] -> acc
    | v :: rest -> (
        match rope v with
        | REmpty -> leaves acc rest
        | RStr s -> leaves (slice s :: acc) rest
        | RCat (a, b) -> leaves acc (a :: b :: rest)
        | RChar c -> leaves ((String.make 1 (Char.chr (Z.to_int (z c))), 0, 1) :: acc) rest)
  in
  let ls = List.rev (leaves [] [ root ]) in
  let total = List.fold_left (fun n (_, _, l) -> n + l) 0 ls in
  let buf = Bytes.create total in
  ignore (List.fold_left (fun pos (s, o, l) -> Bytes.blit_string s o buf pos l; pos + l) 0 ls);
  str (Bytes.unsafe_to_string buf, 0, total)

type 'a array_model = ANil | ACons of 'a * 'a
type 'v list_model = Nil | Cons of 'v * 'v
type 'v pos_model = NoPos | MkPos of 'v * 'v * 'v
type 'v raw_model = RawName of 'v * 'v | RawNat of 'v * 'v | RawChar of 'v * 'v | RawStr of 'v * 'v | RawWild of 'v | RawList of 'v * 'v | RawGen of 'v * 'v * 'v

let pos_view ~str ~nat = function At { file; line; col } -> MkPos (str file, nat line, nat col) | NoLoc | Unknown -> NoPos

let raw_view ~get ~str ~nat ~pos ~list ~raw v =
  let p l = pos (pos_view ~str ~nat l) in
  match get v with
  | Atom (l, Src s) -> RawName (p l, str s)
  | Atom (l, Gen (n, s)) -> RawGen (p l, nat n, str s)
  | Nat (l, n) -> RawNat (p l, nat n)
  | Char (l, c) -> RawChar (p l, nat (Z.of_int c))
  | Str (l, s) -> RawStr (p l, str s)
  | Wild l -> RawWild (p l)
  | List (l, xs) -> RawList (p l, List.fold_right (fun x rest -> list (Cons (raw x, rest))) xs (list Nil))

let raw_fields = function
  | RawName (p, s) -> (0, [ p; s ]) | RawNat (p, n) -> (1, [ p; n ]) | RawChar (p, c) -> (2, [ p; c ])
  | RawStr (p, s) -> (3, [ p; s ]) | RawWild p -> (4, [ p ]) | RawList (p, xs) -> (5, [ p; xs ]) | RawGen (p, n, s) -> (6, [ p; n; s ])
let raw_model i fs = match (i, fs) with
  | 0, [ p; s ] -> RawName (p, s) | 1, [ p; n ] -> RawNat (p, n) | 2, [ p; c ] -> RawChar (p, c)
  | 3, [ p; s ] -> RawStr (p, s) | 4, [ p ] -> RawWild p | 5, [ p; xs ] -> RawList (p, xs) | 6, [ p; n; s ] -> RawGen (p, n, s) | _ -> invalid_arg "raw_model"

let raw_of ~text ~z ~pos ~list ~raw m =
  let l p = match pos p with NoPos -> NoLoc | MkPos (f, line, col) -> At { file = text f; line = z line; col = z col } in
  let rec items v = match list v with Nil -> [] | Cons (x, rest) -> raw x :: items rest in
  match m with
  | RawName (p, s) -> Atom (l p, Src (text s))
  | RawGen (p, n, s) -> Atom (l p, Gen (z n, text s))
  | RawNat (p, n) -> Nat (l p, z n)
  | RawChar (p, c) -> Char (l p, Z.to_int (z c))
  | RawStr (p, s) -> Str (l p, text s)
  | RawWild p -> Wild (l p)
  | RawList (p, xs) -> List (l p, items xs)

(* No host float is ever a value of the language, so no array is a flat float array, and an extracted template
   types an array's elements as [word] rather than [Obj.t], which lets OCaml skip its float check on each access.
   A word may be an immediate or a pointer, as [word]'s own values are, and never a float. *)
type word = Imm | Ptr of int

let array_view ~array ~wrap v =
  let a = array v in
  let length = Array.length a in
  if length = 0 then ANil else ACons (Obj.magic (Array.unsafe_get (Obj.magic a : word array) 0), wrap (Array.sub a 1 (length - 1)))

let array_of ~array ~wrap = function ANil -> wrap [||] | ACons (x, tail) -> wrap (Array.append [| x |] (array tail))
let array_new ~blank n = Array.make (Z.to_int n) blank
let array_make n x = array_new ~blank:x n

let array_swap a i x =
  let a = (Obj.magic a : word array) in
  let old = Array.unsafe_get a (small i) in
  Array.unsafe_set a (small i) (Obj.magic x : word);
  Obj.magic old

let array_pluck a i = Obj.magic (Array.unsafe_get (Obj.magic a : word array) (small i))
let array_get = array_pluck
let array_get_many = array_pluck
let array_place a i x = Array.unsafe_set (Obj.magic a : word array) (small i) (Obj.magic x : word)
let array_length a = Z.of_int (Array.length a)
let array_length_many = array_length
let array_swap_imm a i x =
  let a = (Obj.magic a : int array) in
  let old = Array.unsafe_get a (small i) in
  Array.unsafe_set a (small i) (Obj.magic x : int);
  Obj.magic old

let array_place_imm a i x = Array.unsafe_set (Obj.magic a : int array) (small i) (Obj.magic x : int)
let list_to_array ~list v = let rec go acc v = match list v with Nil -> Array.of_list (List.rev acc) | Cons (x, rest) -> go (x :: acc) rest in go [] v

let byte (b : bytes) i = Z.of_int (Char.code (Bytes.unsafe_get b i))
let bytes_view ~bytes ~u8 ~wrap v =
  let b = bytes v in
  let length = Bytes.length b in
  if length = 0 then ANil else ACons (u8 (byte b 0), wrap (Bytes.sub b 1 (length - 1)))

let bytes_of ~z ~bytes ~wrap = function ANil -> wrap Bytes.empty | ACons (x, tail) -> wrap (Bytes.cat (Bytes.make 1 (Char.unsafe_chr (small (z x)))) (bytes tail))
let bytes_make n x = Bytes.make (Z.to_int n) (Char.unsafe_chr (small x))
let bytes_get b i = byte b (small i)
let bytes_get_many = bytes_get
let bytes_set b i x = Bytes.unsafe_set b (small i) (Char.unsafe_chr (small x))
let bytes_length b = Z.of_int (Bytes.length b)
let bytes_length_many = bytes_length
let str_bytes_copy (s, o, l) = Bytes.of_string (String.sub s o l)
let bytes_str b = (Bytes.unsafe_to_string b, 0, Bytes.length b)
let bytes_copy = Bytes.copy
let array_copy = Array.copy
external array_unsafe_sub : 'a array -> int -> int -> 'a array = "caml_array_sub"
external array_unsafe_blit : 'a array -> int -> 'a array -> int -> int -> unit = "caml_array_blit"
let bytes_sub b i n = let r = Bytes.create (small n) in Bytes.unsafe_blit b (small i) r 0 (small n); r
let bytes_blit src i dst j n = Bytes.unsafe_blit src (small i) dst (small j) (small n)
let array_sub a i n = array_unsafe_sub a (small i) (small n)
let array_blit src i dst j n = array_unsafe_blit src (small i) dst (small j) (small n)
