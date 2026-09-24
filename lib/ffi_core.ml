type slice = string * int * int

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
let str_view ~slice ~u8 ~str v = let s, o, l = slice v in if l = 0 then SNil else SCons (u8 (Z.of_int (Char.code s.[o])), str (s, o + 1, l - 1))
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
  String.iter (fun c -> Buffer.add_string buf (match c with '"' -> "\\\"" | '\\' -> "\\\\" | '\n' -> "\\n" | '\t' -> "\\t" | c -> String.make 1 c)) s;
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
let small (a : Z.t) : int = Obj.magic a
let u62 f a b : Z.t = Obj.magic (f (small a) (small b) : int)
let u62_add = u62 ( + )
let u62_sub = u62 ( - )
let u62_mul = u62 ( * )
let u62_div = u62 ( / )
let u62_mod = u62 ( mod )
let u62_divmod a b = (u62_div a b, u62_mod a b)
let u62_cmp a b = order (compare (small a) (small b))
let u62_lt_dec a b = decide (small a < small b)
let trim (s, o, l) = (String.sub s o l, 0, l)
let str_cmp (s1, o1, l1) (s2, o2, l2) =
  let n = min l1 l2 in
  let rec go i =
    if i = n then if l1 < l2 then CLt else if l1 = l2 then CEq else CGt
    else if s1.[o1 + i] < s2.[o2 + i] then CLt
    else if s1.[o1 + i] > s2.[o2 + i] then CGt
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

let array_view ~array ~wrap v =
  let a, offset, length = array v in
  if length = 0 then ANil else ACons (Array.unsafe_get a offset, wrap (a, offset + 1, length - 1))

let array_of ~array ~wrap = function
  | ANil -> wrap ([||], 0, 0)
  | ACons (x, tail) ->
      let a, offset, length = array tail in
      let result = Array.make (length + 1) x in
      Array.blit a offset result 1 length;
      wrap (result, 0, length + 1)

let array_new ~blank n =
  let length = Z.to_int n in
  (Array.make length blank, 0, length)

let array_swap (a, offset, _) i x =
  let index = offset + small i in
  let old = Array.unsafe_get a index in
  Array.unsafe_set a index x;
  old

let array_pluck (a, offset, _) i = Array.unsafe_get a (offset + small i)
let array_get = array_pluck
let array_place (a, offset, _) i x = Array.unsafe_set a (offset + small i) x
