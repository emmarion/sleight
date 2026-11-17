[@@@warning "-a"]
[@@@alert "-all"]
module Ffi_core = struct
module Cast = struct
  external to_any : 'a -> Obj.t = "%identity"
  external of_any : Obj.t -> 'a = "%identity"
  external cast : 'a -> 'b = "%identity"
end
open Cast

type slice = string * int * int

type loc = At of { file : string; line : Z.t; col : Z.t } | NoLoc | Unknown | Framed of int * loc
type name = Src of string | Gen of Z.t * string
type mult = Erased | Many | Unique
type reading = MintedIs | MintedType
type raw = Atom of loc * name | Handle of loc * int * reading * mult * Obj.t | Wild of loc | Nat of loc * Z.t | Char of loc * int | Str of loc * string | List of loc * raw list

(* Each extern type one level deep, in the order and arities of its model's constructors: [_view] takes a host
   value apart into the constructor at the top and host values below, [_of] puts one together. *)
type 'v nat = Zero | Succ of 'v
type 'v half = HZ | H1 of 'v | H2 of 'v
type 'v str = SNil | SCons of 'v * 'v
type 'v rope = REmpty | RStr of 'v | RCat of 'v * 'v | RChar of 'v
type cmp = CLt | CEq | CGt
type dec = Yes | No
type eq_dec = Equal | Unequal
type bit = Bit0 | Bit1

let () = if Sys.int_size <> 63 || not (Obj.is_int (to_any (Z.of_int max_int))) then failwith "this runtime needs 63-bit ints, and zarith holding every value below 2^62 unboxed"
let () = if Sys.max_array_length >= 1 lsl 54 || Sys.max_string_length >= 1 lsl 57 then failwith "this runtime needs arrays shorter than 2^54 and byte strings shorter than 2^57"

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
(* An application's rendering (section 45): a last argument that is itself an application keeps its own parens
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
let nat_zero_dec a = decide (Z.equal a Z.zero)
let eq_dec b = if b then Equal else Unequal
let bit b = if b then Bit1 else Bit0
let nat_eq a b = eq_dec (Z.equal a b)
let bit_length n = Z.of_int (Z.numbits n)
let bit_test n k = bit (Z.fits_int k && Z.testbit n (Z.to_int k))
let nat_mod = Z.rem
let nat_halve n = n
let shl n k = if n == Z.zero then Z.zero else Z.shift_left n (Z.to_int k)
let nat_and = Z.logand
let nat_or = Z.logor
let nat_xor = Z.logxor
let shr n k = if Z.fits_int k then Z.shift_right n (Z.to_int k) else Z.zero
let small (a : Z.t) : int = cast a
let u62 f a b : Z.t = cast (f (small a) (small b) : int)
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
let u62_inc a : Z.t = cast (small a + 1 : int)
let u62_dec a : Z.t = cast (small a - 1 : int)
let u62_divmod a b = (u62_div a b, u62_mod a b)
let u62_cmp a b = order (compare (small a) (small b))
let u62_lt_dec a b = decide (small a < small b)
let nat_fits_u62 a = decide (Obj.is_int (to_any a))
let u62_eq a b = eq_dec (small a = small b)
let u62_bit_length = bit_length
let u62_bit_test n k = bit ((small n lsr small k) land 1 = 1)
let popcount n = Z.of_int (Z.popcount n)
let trailing_zeros n = Z.of_int (Z.trailing_zeros n)
let u62_popcount n : Z.t =
  let x = small n in
  let x = x - ((x lsr 1) land 0x1555555555555555) in
  let x = (x land 0x3333333333333333) + ((x lsr 2) land 0x3333333333333333) in
  cast ((((x + (x lsr 4)) land 0x0f0f0f0f0f0f0f0f) * 0x0101010101010101) lsr 56 : int)
let u62_trailing_zeros = trailing_zeros
let trim (s, o, l) = (String.sub s o l, 0, l)
let str_cmp (s1, o1, l1) (s2, o2, l2) =
  let n = if l1 < l2 then l1 else l2 in
  let rec go i =
    if i = n then if l1 < l2 then CLt else if l1 = l2 then CEq else CGt
    else if String.unsafe_get s1 (o1 + i) < String.unsafe_get s2 (o2 + i) then CLt
    else if String.unsafe_get s1 (o1 + i) > String.unsafe_get s2 (o2 + i) then CGt
    else go (i + 1)
  in
  go 0
let str_length (_, _, l) = Z.of_int l
let str_eq (s1, o1, l1) (s2, o2, l2) =
  let rec go i = i = l1 || (String.unsafe_get s1 (o1 + i) = String.unsafe_get s2 (o2 + i) && go (i + 1)) in
  eq_dec (l1 = l2 && go 0)
let str_get (s, o, _) i = Z.of_int (Char.code (String.unsafe_get s (o + Z.to_int i)))
let str_split (s, o, l) k = let k = Z.to_int k in ((s, o, k), (s, o + k, l - k))
let nat_str n = let s = Z.to_string n in (s, 0, String.length s)
let str_nat (s, o, l) =
  let rec digits i = i = l || (s.[o + i] >= '0' && s.[o + i] <= '9' && digits (i + 1)) in
  if l > 0 && digits 0 && (l = 1 || s.[o] <> '0') then Some (Z.of_substring s ~pos:o ~len:l) else None
let nat_of_string s = str_nat (s, 0, String.length s)
let append ((s1, o1, l1) as a) ((s2, o2, l2) as b) =
  if l1 = 0 then b else if l2 = 0 then a
  else let buf = Bytes.create (l1 + l2) in Bytes.blit_string s1 o1 buf 0 l1; Bytes.blit_string s2 o2 buf l1 l2; (Bytes.unsafe_to_string buf, 0, l1 + l2)

(* A rope flattened into one buffer, its leaves in order, or a lone string leaf as it is. [rope] views a node,
   [slice] and [z] read the two kinds of leaf, [str] makes the result. *)
let flatten ~rope ~slice ~z ~str root =
  match rope root with
  | RStr s -> str (slice s)
  | _ ->
      let rec walk leaf acc = function
        | [] -> acc
        | v :: rest -> (
            match rope v with
            | REmpty -> walk leaf acc rest
            | RCat (a, b) -> walk leaf acc (a :: b :: rest)
            | node -> walk leaf (leaf acc node) rest)
      in
      let buf = Bytes.create (walk (fun n -> function RStr s -> let _, _, l = slice s in n + l | RChar _ -> n + 1 | _ -> n) 0 [ root ]) in
      let n =
        walk
          (fun j -> function
            | RStr s -> let s, o, l = slice s in Bytes.blit_string s o buf j l; j + l
            | RChar c -> Bytes.set buf j (Char.chr (Z.to_int (z c))); j + 1
            | _ -> j)
          0 [ root ]
      in
      str (Bytes.unsafe_to_string buf, 0, n)

type 'a array_model = ANil | ACons of 'a * 'a
type 'v list_model = Nil | Cons of 'v * 'v
type 'v pos_model = NoPos | MkPos of 'v * 'v * 'v
type 'v symbol_model = SName of 'v | SGen of 'v * 'v
type 'v raw_model = RawSymbol of 'v * 'v | RawWild of 'v | RawList of 'v * 'v | RawSettled of 'v * 'v

let rec pos_view ~str ~nat = function At { file; line; col } -> MkPos (str file, nat line, nat col) | NoLoc | Unknown -> NoPos | Framed (_, l) -> pos_view ~str ~nat l

let raw_view ~handle ~symbol ~get ~str ~nat ~pos ~list ~raw v =
  let p l = pos (pos_view ~str ~nat l) in
  match get v with
  | Atom (l, Src s) -> RawSymbol (p l, symbol (SName (str s)))
  | Atom (l, Gen (n, s)) -> RawSymbol (p l, symbol (SGen (nat n, str s)))
  | Handle (l, x, r, m, v) -> RawSettled (p l, handle (x, r, m, v))
  | Nat _ | Char _ | Str _ -> invalid_arg "raw_view: a literal is a handle in a macro's arguments"
  | Wild l -> RawWild (p l)
  | List (l, xs) -> RawList (p l, List.fold_right (fun x rest -> list (Cons (raw x, rest))) xs (list Nil))

let raw_fields = function
  | RawSymbol (p, s) -> (0, [ p; s ]) | RawWild p -> (1, [ p ]) | RawList (p, xs) -> (2, [ p; xs ]) | RawSettled (p, h) -> (3, [ p; h ])
let raw_model i fs = match (i, fs) with
  | 0, [ p; s ] -> RawSymbol (p, s) | 1, [ p ] -> RawWild p | 2, [ p; xs ] -> RawList (p, xs) | 3, [ p; h ] -> RawSettled (p, h) | _ -> invalid_arg "raw_model"

let raw_of ~unhandle ~unsymbol ~text ~z ~pos ~list ~raw m =
  let l p = match pos p with NoPos -> NoLoc | MkPos (f, line, col) -> At { file = text f; line = z line; col = z col } in
  let rec items v = match list v with Nil -> [] | Cons (x, rest) -> raw x :: items rest in
  match m with
  | RawSymbol (p, s) -> Atom (l p, match unsymbol s with SName t -> Src (text t) | SGen (n, t) -> Gen (z n, text t))
  | RawSettled (p, h) -> unhandle (l p) h
  | RawWild p -> Wild (l p)
  | RawList (p, xs) -> List (l p, items xs)

(* No host float is ever a value of the language, so no array is a flat float array, and an extracted template
   types an array's elements as [word] rather than [Obj.t], which lets OCaml skip its float check on each access.
   A word may be an immediate or a pointer, never a float. *)
type word = ..

let array_view ~array ~wrap v =
  let a = array v in
  let length = Array.length a in
  if length = 0 then ANil else ACons (cast (Array.unsafe_get (cast a : word array) 0), wrap (Array.sub a 1 (length - 1)))

let array_of ~array ~wrap = function ANil -> wrap [||] | ACons (x, tail) -> wrap (Array.append [| x |] (array tail))
let array_new ~blank n = Array.make (Z.to_int n) blank
let array_make n x = array_new ~blank:x n

let array_swap a i x =
  let a = (cast a : word array) in
  let old = Array.unsafe_get a (small i) in
  Array.unsafe_set a (small i) (cast x : word);
  cast old

let array_pluck a i = cast (Array.unsafe_get (cast a : word array) (small i))
let array_get = array_pluck
let array_get_many = array_pluck
let array_place a i x = Array.unsafe_set (cast a : word array) (small i) (cast x : word)
let array_length a = Z.of_int (Array.length a)
let array_length_many = array_length
let array_length_dec (_ : 'a array) = Yes
let array_length_dec_many = array_length_dec
let array_swap_imm a i x =
  let a = (cast a : int array) in
  let old = Array.unsafe_get a (small i) in
  Array.unsafe_set a (small i) (cast x : int);
  cast old

let array_place_imm a i x = Array.unsafe_set (cast a : int array) (small i) (cast x : int)
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
let bytes_length_dec (_ : bytes) = Yes
let bytes_length_dec_many = bytes_length_dec
let str_bytes_copy (s, o, l) = let b = Bytes.create l in Bytes.blit_string s o b 0 l; b
let bytes_str b = (Bytes.unsafe_to_string b, 0, Bytes.length b)
let bytes_copy = Bytes.copy
external bytes_get16u : bytes -> int -> int = "%caml_bytes_get16u"
external bytes_set16u : bytes -> int -> int -> unit = "%caml_bytes_set16u"
external bytes_get32u : bytes -> int -> int32 = "%caml_bytes_get32u"
external bytes_set32u : bytes -> int -> int32 -> unit = "%caml_bytes_set32u"
external string_get16u : string -> int -> int = "%caml_string_get16u"
external string_get32u : string -> int -> int32 = "%caml_string_get32u"
external swap16 : int -> int = "%bswap16"
external swap32 : int32 -> int32 = "%bswap_int32"
let le16 x = if Sys.big_endian then swap16 x else x
let le32 x = if Sys.big_endian then swap32 x else x
let u32 x = Int32.to_int (le32 x) land 0xFFFF_FFFF
let le_get16 b i = le16 (bytes_get16u b i)
let le_get32 b i = u32 (bytes_get32u b i)
let le_set16 b i v = bytes_set16u b i (le16 v)
let le_set32 b i v = bytes_set32u b i (le32 (Int32.of_int v))
let le_sget16 s i = le16 (string_get16u s i)
let le_sget32 s i = u32 (string_get32u s i)
let bytes_get16 b i = Z.of_int (le_get16 b (small i))
let bytes_get16_many = bytes_get16
let bytes_get32 b i = Z.of_int (le_get32 b (small i))
let bytes_get32_many = bytes_get32
let bytes_set16 b i v = le_set16 b (small i) (small v)
let bytes_set32 b i v = le_set32 b (small i) (small v)
let str_get16 (s, o, _) i = Z.of_int (le_sget16 s (o + small i))
let str_get32 (s, o, _) i = Z.of_int (le_sget32 s (o + small i))
let bytes_fill b i n x = Bytes.unsafe_fill b (small i) (small n) (Char.unsafe_chr (small x))
external bytes_get64u : bytes -> int -> int64 = "%caml_bytes_get64u"
external swap64 : int64 -> int64 = "%bswap_int64"
let be64 x = if Sys.big_endian then x else swap64 x
let range_compare a i m b j n =
  if i = 0 && j = 0 && m = Bytes.length a && n = Bytes.length b then Bytes.compare a b else
  let len = if m < n then m else n in
  let rec bytewise k =
    if k = len then compare m n
    else let c = Char.code (Bytes.unsafe_get a (i + k)) - Char.code (Bytes.unsafe_get b (j + k)) in if c <> 0 then c else bytewise (k + 1) in
  let rec words k =
    if k + 8 > len then bytewise k
    else let x = bytes_get64u a (i + k) and y = bytes_get64u b (j + k) in
      if Int64.equal x y then words (k + 8) else Int64.unsigned_compare (be64 x) (be64 y) in
  words 0
let bytes_cmp a i m b j n = order (range_compare a (small i) (small m) b (small j) (small n))
let bytes_cmp_many = bytes_cmp
let bytes_cmp_unique_many = bytes_cmp
let array_copy = Array.copy
external array_unsafe_sub : 'a array -> int -> int -> 'a array = "caml_array_sub"
external array_unsafe_blit : 'a array -> int -> 'a array -> int -> int -> unit = "caml_array_blit"
let bytes_sub b i n = let r = Bytes.create (small n) in Bytes.unsafe_blit b (small i) r 0 (small n); r
let bytes_blit src i dst j n = Bytes.unsafe_blit src (small i) dst (small j) (small n)
let bytes_blit_many = bytes_blit
let array_sub a i n = array_unsafe_sub a (small i) (small n)
let array_blit src i dst j n = array_unsafe_blit src (small i) dst (small j) (small n)
let array_blit_many = array_blit
let array_move = array_blit
(* Array.blit calls caml_modify per element when the destination is in the major heap, immediates included
   (runtime/array.c, 4.14 through 5.5). caml_blit_bytes is a plain memmove there; on 4.14.1 it measured
   4-18x faster than Array.blit on an old destination and about even on a young one. *)
external blit_words : Obj.t -> int -> Obj.t -> int -> int -> unit = "caml_blit_bytes" [@@noalloc]
let array_blit_imm src i dst j n = let w = Sys.word_size / 8 in blit_words (to_any src) (small i * w) (to_any dst) (small j * w) (small n * w)
let array_blit_many_imm = array_blit_imm
let array_move_imm = array_blit_imm

type slot_find = SlotFound of int | SlotMissing
type slot_intern = SlotExisting of int | SlotAdded of int

type slots = {
  mutable keys : word array;  (* the slot of each id, the oldest at 0 *)
  mutable count : int;  (* the ids in use, so the next one to give out; at most the length of [keys] *)
  old : (int, int) Hashtbl.t;  (* address to id for the ids below [young_from], whose blocks a minor collection has promoted *)
  young : (int, int) Hashtbl.t;  (* address to id for the ids from [young_from], valid until the next minor collection *)
  mutable young_from : int;  (* the first id given out since [sentinel] was allocated *)
  mutable sentinel : int ref;  (* a block allocated young, which the next minor collection moves *)
  mutable sentinel_at : int;  (* [sentinel]'s address when it was allocated *)
  mutable compactions_seen : int }  (* [compactions] when [old] was last built; -1 forces a rebuild *)

let address (x : word) : int = 2 * (Obj.magic (Sys.opaque_identity x) : int)
(* An earlier version counted compactions with a GC alarm, as below. It appeared to work on OCaml 5.5.1 but not
   on 4.14.1, where Gc.compact seemed to run the alarm before compacting, so the count lagged a major cycle and
   lookups after a compaction could miss (tests/slots_compact.sl):
     let compactions = ref 0
     let watch_compactions =
       lazy
         (let seen = ref (Gc.quick_stat ()).compactions in
          ignore (Gc.create_alarm (fun () -> let c = (Gc.quick_stat ()).compactions in if c <> !seen then (seen := c; incr compactions)))) *)
let compactions () = (Gc.quick_stat ()).compactions

let renew_sentinel t = let s = ref 0 in t.sentinel <- s; t.sentinel_at <- address (cast s)
let moved t = address (cast t.sentinel) <> t.sentinel_at

let rec sync t =
  if t.compactions_seen <> compactions () then begin
    t.compactions_seen <- compactions ();
    Hashtbl.reset t.old;
    for i = 0 to t.count - 1 do Hashtbl.add t.old (address t.keys.(i)) i done;
    Hashtbl.reset t.young; t.young_from <- t.count; renew_sentinel t; sync t
  end
  else if moved t then begin
    for i = t.young_from to t.count - 1 do Hashtbl.add t.old (address t.keys.(i)) i done;
    Hashtbl.reset t.young; t.young_from <- t.count; renew_sentinel t; sync t
  end

let slots_new () =
  { keys = [||]; count = 0; old = Hashtbl.create 16; young = Hashtbl.create 16; young_from = 0;
    sentinel = ref 0; sentinel_at = 0; compactions_seen = -1 }

let rec slots_lookup t (s : word) =
  sync t;
  let compacted = t.compactions_seen and a = address s in
  let hit = List.find_opt (fun i -> t.keys.(i) == s) in
  let r = match hit (Hashtbl.find_all t.young a) with Some i -> Some i | None -> hit (Hashtbl.find_all t.old a) in
  ignore (Sys.opaque_identity (ref ()));
  if moved t || compacted <> compactions () then slots_lookup t s else r

let slots_find t s = match slots_lookup t (cast s) with Some i -> SlotFound i | None -> SlotMissing

let slots_add t s =
  let s = (cast s : word) and i = t.count in
  sync t;
  if i = Array.length t.keys then begin
    let keys = Array.make (max 8 (2 * i)) s in
    Array.blit t.keys 0 keys 0 i; t.keys <- keys
  end;
  t.keys.(i) <- s; t.count <- i + 1;
  Hashtbl.add t.young (address s) i; sync t;
  i

let slots_intern t s = match slots_lookup t (cast s) with Some i -> SlotExisting i | None -> SlotAdded (slots_add t s)

let slots_length t = t.count
let slots_keys t = Array.sub t.keys 0 t.count

type 'v slots_model = MkSlots of 'v
let slots_view ~slots ~list v = MkSlots (Array.fold_left (fun rest k -> list (Cons (cast k, rest))) (list Nil) (slots_keys (slots v)))
let slots_of ~list ~wrap (MkSlots l) =
  let rec oldest_first acc v = match list v with Nil -> acc | Cons (k, rest) -> oldest_first (k :: acc) rest in
  let t = slots_new () in
  List.iter (fun k -> ignore (slots_add t k)) (oldest_first [] l);
  wrap t
end
module Driver_core = struct
type fence = { reads : string list; writes : string list }

type world = {
  read_rest : unit -> string;
  read_line : unit -> string option;
  out : string -> int -> int -> unit;
  err : string -> int -> int -> unit;
  args : string list;
  env : string -> string option;
  envs : unit -> (string * string) list;
  cwd : unit -> string;
  exit : int -> unit;
  print : string -> unit;
  exec : bool;
  fence : fence ref;
  limit : int option ref;
  used : int ref;
}

type 'v request =
  | WriteOut of 'v
  | WriteErr of 'v
  | ReadLine
  | ReadFile of 'v
  | ReadFileIn of 'v * 'v
  | WriteFile of 'v * 'v
  | GetArgs
  | GetEnv of 'v
  | GetEnvs
  | AppendFile of 'v * 'v
  | ReadRemaining
  | ListDir of 'v
  | GetCwd
  | Stat of 'v
  | MkDir of 'v
  | DeleteFile of 'v
  | DeleteDir of 'v
  | ConfinePaths of 'v * 'v
  | ConfineOutputBytes of 'v
  | Measure of 'v
  | Exec of 'v * 'v

type 'v step = Exit of 'v | Continue of 'v

(* What the driver builds and reads of the prelude, each a direct operation on the program's own values. *)
type 'v ops = {
  zero : 'v;
  succ : 'v -> 'v;
  pred : 'v -> 'v option;
  u8 : 'v -> 'v;
  un_u8 : 'v -> 'v;
  char : 'v -> 'v;
  un_char : 'v -> 'v;
  snil : 'v;
  scons : 'v -> 'v -> 'v;
  un_str : 'v -> ('v * 'v) option;
  un_list : 'v -> ('v * 'v) option;
  un_pair : 'v -> 'v * 'v;
  un_some : 'v -> 'v option;
  some : 'v -> 'v;
  none : 'v;
  ok : 'v -> 'v;
  fail : 'v -> 'v;
  unit : 'v;
  cons : 'v -> 'v -> 'v;
  nil : 'v;
  pair : 'v -> 'v -> 'v;
  is_file : 'v;
  is_dir : 'v;
  is_other : 'v;
  missing : 'v;
  changed : 'v;
  unchanged : 'v;
  mk_usage : 'v;
  mk_exited : 'v;
  un_job : 'v -> 'v * 'v * 'v * 'v * 'v;
  exec_results : 'v -> 'v;
  request : 'v -> 'v request;
  step : 'v -> 'v step;
  is_start : 'v -> bool;
  apply : 'v -> 'v list -> 'v;
}

type 'v t = { of_string : string -> 'v; to_string : 'v -> string; perform : world -> 'v -> 'v; run_program : world -> 'v -> int; run_main : world -> 'v -> unit }

exception Halt of int

let read_file path = In_channel.with_open_bin path In_channel.input_all
let save flags path (s, o, l) = Out_channel.with_open_gen flags 0o666 path (fun oc -> Out_channel.output_substring oc s o l)
let replacing = [ Open_wronly; Open_creat; Open_trunc; Open_binary ]
let write_file path s = save replacing path (s, 0, String.length s)
let explain = function Unix.Unix_error (e, _, a) -> (if a = "" then "" else a ^ ": ") ^ Unix.error_message e | Sys_error m -> m | e -> Printexc.to_string e
let is_dir p = match (Unix.stat p).st_kind with Unix.S_DIR -> true | _ -> false | exception _ -> false
let parts p = List.filter (fun c -> c <> "" && c <> ".") (String.split_on_char '/' p)
let path cs = "/" ^ String.concat "/" cs

let resolve ~follow p =
  let follow = follow || List.mem (Filename.basename p) [ "."; ".." ] || String.ends_with ~suffix:"/" p in
  let rec go budget up = function
    | [] -> List.rev up
    | ".." :: rest -> go budget (match up with [] -> [] | _ :: above -> above) rest
    | c :: rest -> (
        let here = path (List.rev (c :: up)) in
        match (Unix.lstat here).st_kind with
        | Unix.S_LNK when follow || rest <> [] -> (
            match Unix.readlink here with
            | _ when budget = 0 -> raise (Sys_error (p ^ ": too many levels of symbolic links"))
            | target -> go (budget - 1) (if Filename.is_relative target then up else []) (parts target @ rest))
        | _ -> go budget (c :: up) rest
        | exception Unix.Unix_error _ when rest = [] -> List.rev (c :: up))
  in
  go 1000 [] (parts (if Filename.is_relative p then Sys.getcwd () ^ "/" ^ p else p))

let rec prefix = function [], _ -> true | f :: fs, c :: cs -> f = c && prefix (fs, cs) | _ :: _, [] -> false
let covers dirs cs = List.exists (fun d -> prefix (parts d, cs)) dirs

let resolved ~follow p = match resolve ~follow p with cs -> Ok cs | exception ((Sys_error _ | Unix.Unix_error _) as e) -> Error (explain e)
let inside dir ~follow p = Result.map (fun cs -> if covers [ dir ] cs then Some cs else None) (resolved ~follow p)

type access = Read | Write

let unconfined = { reads = []; writes = [ "/" ] }
let reaches f access cs = covers (match access with Read -> f.reads @ f.writes | Write -> f.writes) cs
let outside access p = Error (p ^ ": outside the " ^ (match access with Read -> "readable" | Write -> "writable") ^ " paths")

let admits fence access ~follow p =
  Result.bind (resolved ~follow p) (fun cs -> if reaches !fence access cs then Ok cs else outside access p)

let within dir p =
  match path (resolve ~follow:true dir) with
  | exception Unix.Unix_error (Unix.ENOENT, _, _) -> Error (p ^ ": no directory " ^ dir)
  | exception ((Sys_error _ | Unix.Unix_error _) as e) -> Error (explain e)
  | d when not (is_dir d) -> Error (p ^ ": no directory " ^ dir)
  | d ->
      let full = if Filename.is_relative p then d ^ "/" ^ p else p in
      let named m = p ^ if String.starts_with ~prefix:(full ^ ":") m then String.sub m (String.length full) (String.length m - String.length full) else ": " ^ m in
      Result.bind (Result.map_error named (inside d ~follow:true full)) (function
        | None -> Error (p ^ ": outside the directory " ^ dir)
        | Some _ -> Ok (full, fun () -> match read_file full with s -> Ok s | exception Sys_error m -> Error (named m)))

let read_within dir p = Result.bind (within dir p) (fun (_, read) -> read ())

let confine fence reads writes =
  let entry access e = Result.bind (resolved ~follow:true e) (fun cs -> if reaches !fence access cs then Ok (path cs) else outside access e) in
  let rec all access = function [] -> Ok [] | e :: es -> Result.bind (entry access e) (fun p -> Result.map (List.cons p) (all access es)) in
  Result.bind (all Read reads) (fun reads -> Result.map (fun writes -> fence := { reads; writes }) (all Write writes))

let restrict fence reads writes = if reads = [] && writes = [] then Ok () else confine fence reads writes

let entry_bytes = 4096
let clamp z = if Z.fits_int z then Some (Z.to_int z) else None

let output_limit b =
  match Ffi_core.nat_of_string b with Some z -> Ok (clamp z) | None -> Error (b ^ ": not a number of bytes")

let start reads writes bytes env exec w =
  let fail m = prerr_endline m; exit 1 in
  Result.iter_error fail (restrict w.fence reads writes);
  Option.iter (fun b -> w.limit := Result.fold ~ok:Fun.id ~error:fail (output_limit b)) bytes;
  let w = { w with exec = w.exec && exec } in
  if env then w else { w with env = (fun _ -> None); envs = (fun () -> []) }

let signal_names =
  Sys.[ (sigabrt, "SIGABRT"); (sigalrm, "SIGALRM"); (sigfpe, "SIGFPE"); (sighup, "SIGHUP"); (sigill, "SIGILL"); (sigint, "SIGINT");
        (sigkill, "SIGKILL"); (sigpipe, "SIGPIPE"); (sigquit, "SIGQUIT"); (sigsegv, "SIGSEGV"); (sigterm, "SIGTERM"); (sigusr1, "SIGUSR1");
        (sigusr2, "SIGUSR2"); (sigbus, "SIGBUS"); (sigtrap, "SIGTRAP"); (sigxcpu, "SIGXCPU"); (sigxfsz, "SIGXFSZ") ]

let found prog env =
  let runnable p = Sys.file_exists p && not (is_dir p) && (try Unix.access p [ Unix.X_OK ]; true with Unix.Unix_error _ -> false) in
  let absolute p = if Filename.is_relative p then Filename.concat (Sys.getcwd ()) p else p in
  if String.contains prog '/' then Ok (absolute prog)
  else
    let dirs = Option.fold ~none:[] ~some:(String.split_on_char ':') (List.assoc_opt "PATH" env) in
    Option.to_result ~none:(prog ^ ": not found on the PATH it was given")
      (List.find_opt runnable (List.map (fun d -> absolute (Filename.concat (if d = "" then "." else d) prog)) dirs))

type job = {
  prog : string; pid : int; input : string; in_w : Unix.file_descr; mutable sent : int;
  mutable readers : (Unix.file_descr * Buffer.t) list; out : Buffer.t; err : Buffer.t; why : Buffer.t;
}

(* The child reports a failure to start through a close-on-exec pipe, which reads empty once the exec succeeds. *)
let spawn (prog, args, env, dir, input) =
  Result.bind (found prog env) (fun path ->
      match
        let in_r, in_w = Unix.pipe ~cloexec:true () and out_r, out_w = Unix.pipe ~cloexec:true () in
        let err_r, err_w = Unix.pipe ~cloexec:true () and why_r, why_w = Unix.pipe ~cloexec:true () in
        match Unix.fork () with
        | 0 ->
            (try
               Option.iter Unix.chdir dir;
               List.iter (fun (a, b) -> Unix.dup2 ~cloexec:false a b) [ (in_r, Unix.stdin); (out_w, Unix.stdout); (err_w, Unix.stderr) ];
               Unix.execve path (Array.of_list (prog :: args)) (Array.of_list (List.map (fun (n, v) -> n ^ "=" ^ v) env))
             with e -> let m = Bytes.of_string (explain e) in ignore (Unix.write why_w m 0 (Bytes.length m)));
            Unix._exit 127
        | pid ->
            List.iter Unix.close [ in_r; out_w; err_w; why_w ];
            Unix.set_nonblock in_w;
            if input = "" then Unix.close in_w;
            let out = Buffer.create 4096 and err = Buffer.create 256 and why = Buffer.create 64 in
            { prog; pid; input; in_w; sent = 0; readers = [ (out_r, out); (err_r, err); (why_r, why) ]; out; err; why }
      with
      | j -> Ok j
      | exception ((Unix.Unix_error _ | Sys_error _) as e) -> Error (prog ^ ": " ^ explain e))

let writing j = j.sent < String.length j.input

let reap j =
  match snd (Unix.waitpid [] j.pid) with
  | _ when Buffer.length j.why > 0 -> Error (j.prog ^ ": " ^ Buffer.contents j.why)
  | Unix.WEXITED code -> Ok (code, Buffer.contents j.out, Buffer.contents j.err)
  | Unix.WSIGNALED s | Unix.WSTOPPED s ->
      Error (j.prog ^ ": killed by signal " ^ Option.value (List.assoc_opt s signal_names) ~default:(string_of_int s))

let pump chunk running =
  let readers = List.concat_map (fun (_, j) -> List.map fst j.readers) running in
  let writers = List.filter_map (fun (_, j) -> if writing j then Some j.in_w else None) running in
  let ready_r, ready_w, _ = try Unix.select readers writers [] (-1.) with Unix.Unix_error (Unix.EINTR, _, _) -> ([], [], []) in
  List.iter
    (fun (_, j) ->
      if writing j && List.mem j.in_w ready_w then begin
        (j.sent <- match Unix.single_write_substring j.in_w j.input j.sent (String.length j.input - j.sent) with
          | n -> j.sent + n
          | exception Unix.Unix_error ((Unix.EAGAIN | Unix.EINTR), _, _) -> j.sent
          | exception Unix.Unix_error (Unix.EPIPE, _, _) -> String.length j.input);
        if not (writing j) then Unix.close j.in_w
      end;
      j.readers <-
        List.filter
          (fun (fd, buf) ->
            not (List.mem fd ready_r)
            || match Unix.read fd chunk 0 (Bytes.length chunk) with
               | 0 -> Unix.close fd; false
               | n -> Buffer.add_subbytes buf chunk 0 n; true
               | exception Unix.Unix_error (Unix.EINTR, _, _) -> true)
          j.readers)
    running

let exec_all k jobs =
  let results = Array.make (List.length jobs) (Error "") and chunk = Bytes.create 65536 in
  let rec loop pending running =
    match (pending, List.partition (fun (_, j) -> j.readers = [] && not (writing j)) running) with
    | [], ([], []) -> ()
    | _, ((_ :: _ as finished), live) -> List.iter (fun (i, j) -> results.(i) <- reap j) finished; loop pending live
    | (i, job) :: rest, ([], live) when List.length live < k -> (
        match spawn job with Ok j -> loop rest ((i, j) :: live) | Error m -> results.(i) <- Error m; loop rest live)
    | _, ([], live) -> pump chunk live; loop pending live
  in
  let pipe = Sys.signal Sys.sigpipe Sys.Signal_ignore in
  Fun.protect ~finally:(fun () -> Sys.set_signal Sys.sigpipe pipe) (fun () -> loop (List.mapi (fun i job -> (i, job)) jobs) []);
  Array.to_list results

let exec prog args env dir input = List.hd (exec_all 1 [ (prog, args, env, dir, input) ])

let host_envs () =
  List.filter_map
    (fun s -> Option.map (fun i -> (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))) (String.index_opt s '='))
    (Array.to_list (Unix.environment ()))

let processors =
  lazy
    (let ask prog args = match exec prog args (host_envs ()) None "" with Ok (0, out, _) -> int_of_string_opt (String.trim out) | _ -> None in
     match List.find_map (fun (prog, args) -> Option.bind (ask prog args) (fun n -> if n > 0 then Some n else None)) [ ("nproc", []); ("getconf", [ "_NPROCESSORS_ONLN" ]) ] with
     | Some n -> n
     | None -> 1)

let spend w cost =
  match !(w.limit) with
  | None -> true
  | Some limit ->
      cost <= limit - !(w.used) && (w.used := !(w.used) + cost; true)
      || (let m = Printf.sprintf "runtime error: output limit exceeded: this request would bring the program's approximate output to %d bytes, over its limit of %d\n" (!(w.used) + cost) limit in w.err m 0 (String.length m); false)

let print w s = if spend w (String.length s + 1) then w.print s else w.exit 1

let make ?str_of_host ?str_to_slice ?nat_to_z ?nat_of_z o =
  let rec count z v = match o.pred v with Some p -> count (Z.succ z) p | None -> z in
  let to_z = Option.value nat_to_z ~default:(count Z.zero) in
  let u8 v = Z.to_int (to_z (o.un_u8 v)) in
  let nat n = match nat_of_z with Some f -> f (Z.of_int n) | None -> let rec go n = if n = 0 then o.zero else o.succ (go (n - 1)) in go n in
  let of_string s =
    match str_of_host with
    | Some f -> f s
    | None ->
        String.fold_right (fun ch acc -> o.scons (o.char (o.u8 (nat (Char.code ch)))) acc) s o.snil
  in
  let to_slice v =
    match str_to_slice with
    | Some f -> f v
    | None ->
        let buf = Buffer.create 64 in
        let rec go v = match o.un_str v with Some (ch, rest) -> Buffer.add_char buf (Char.chr (u8 (o.un_char ch))); go rest | None -> () in
        go v;
        (Buffer.contents buf, 0, Buffer.length buf)
  in
  let to_string v = let s, i, n = to_slice v in String.sub s i n in
  let started = lazy (Unix.gettimeofday (), Unix.times (), Gc.quick_stat (), Gc.minor_words ()) in
  let perform w req =
    let entered = Gc.minor_words () in
    let result f = match f () with x -> o.ok x | exception ((Unix.Unix_error _ | Sys_error _) as e) -> o.fail (of_string (explain e)) in
    let list of_item xs = List.fold_right (fun x acc -> o.cons (of_item x) acc) xs o.nil in
    let rec items of_item v = match o.un_list v with Some (x, rest) -> of_item x :: items of_item rest | None -> [] in
    let strs = items to_string in
    let change already f =
      match f () with
      | () -> o.ok o.changed
      | exception Unix.Unix_error (e, _, _) when already e -> o.ok o.unchanged
      | exception ((Unix.Unix_error _ | Sys_error _) as e) -> o.fail (of_string (explain e))
    in
    let created p = if Sys.file_exists p then 0 else entry_bytes in
    let fenced ?(access = Read) ?(follow = true) ?(cost = fun _ -> 0) path answer =
      let p = to_string path in
      match admits w.fence access ~follow p with
      | Ok _ -> if spend w (cost p) then answer p else raise (Halt 1)
      | Error m -> o.fail (of_string m)
    in
    let read p = result (fun () -> of_string (read_file p)) in
    let write out s = let t, i, n = to_slice s in if spend w n then (out t i n; o.unit) else raise (Halt 1) in
    let write_to flags path s = let (_, _, n) as x = to_slice s in fenced ~access:Write ~cost:(fun p -> n + created p) path (fun p -> result (fun () -> save flags p x; o.unit)) in
    match o.request req with
    | WriteOut s -> write w.out s
    | WriteErr s -> write w.err s
    | ReadLine -> (match w.read_line () with Some l -> o.some (of_string l) | None -> o.none)
    | ReadFile path -> fenced path read
    | ReadFileIn (dir, path) -> (
        match within (to_string dir) (to_string path) with
        | Ok (full, read) -> fenced (of_string full) (fun _ -> match read () with Ok s -> o.ok (of_string s) | Error m -> o.fail (of_string m))
        | Error m -> o.fail (of_string m))
    | WriteFile (path, s) -> write_to replacing path s
    | GetArgs -> list of_string w.args
    | GetEnv name -> (match w.env (to_string name) with Some v -> o.some (of_string v) | None -> o.none)
    | GetEnvs -> list (fun (n, v) -> o.pair (of_string n) (of_string v)) (List.sort compare (w.envs ()))
    | AppendFile (path, s) -> write_to [ Open_append; Open_creat; Open_wronly ] path s
    | ReadRemaining -> of_string (w.read_rest ())
    | ListDir path -> fenced path (fun p -> result (fun () -> list of_string (List.sort compare (Array.to_list (Sys.readdir p)))))
    | GetCwd -> of_string (w.cwd ())
    | Stat path ->
        fenced path (fun p ->
            match (Unix.stat p).st_kind with
            | Unix.S_REG -> o.ok o.is_file
            | Unix.S_DIR -> o.ok o.is_dir
            | _ -> o.ok o.is_other
            | exception Unix.Unix_error (Unix.ENOENT, _, _) -> o.ok o.missing
            | exception (Unix.Unix_error _ as e) -> o.fail (of_string (explain e)))
    | MkDir path -> fenced ~access:Write ~follow:false ~cost:created path (fun p -> change (fun e -> e = Unix.EEXIST && is_dir p) (fun () -> Unix.mkdir p 0o777))
    | DeleteFile path -> fenced ~access:Write ~follow:false path (fun p -> change (fun e -> e = Unix.ENOENT) (fun () -> Unix.unlink p))
    | DeleteDir path -> fenced ~access:Write ~follow:false path (fun p -> change (fun e -> e = Unix.ENOENT) (fun () -> Unix.rmdir p))
    | ConfinePaths (reads, writes) ->
        (match confine w.fence (strs reads) (strs writes) with Ok () -> o.ok o.unit | Error m -> o.fail (of_string m))
    | ConfineOutputBytes bytes -> (
        let z = to_z bytes in
        match !(w.limit) with
        | Some limit when Option.fold ~none:true ~some:(fun n -> n > limit) (clamp z) ->
            o.fail (of_string (Printf.sprintf "%s bytes: above the current output limit of %d bytes" (Z.to_string z) limit))
        | _ -> w.limit := clamp z; o.ok o.unit)
    | Measure c ->
        let reading m1 extra =
          let g1 = Gc.quick_stat () in
          let c1 = Unix.times () in
          let t1 = Unix.gettimeofday () in
          let t0, c0, g0, m0 = Lazy.force started in
          let words f = f g1 -. f g0 and count f = float_of_int (f g1 - f g0) and ns f = 1e9 *. (f c1 -. f c0) in
          let nat x = match nat_of_z with Some f -> f (Z.of_float (Float.round (Float.max 0. x))) | None -> o.zero in
          o.apply o.mk_usage
            (List.map nat
               [ 1e9 *. (t1 -. t0); ns (fun c -> c.Unix.tms_utime); ns (fun c -> c.Unix.tms_stime);
                 m1 -. m0 +. extra; words (fun g -> g.Gc.promoted_words); words (fun g -> g.Gc.major_words -. g.Gc.promoted_words);
                 count (fun g -> g.Gc.minor_collections); count (fun g -> g.Gc.major_collections) ])
        in
        (* Start counts the words its throwaway build allocates and adds them to its reading, which is right only
           if the real build allocates the same words. Hiding the closure and its argument from the optimizer keeps
           the two calls compiled alike; without it, flambda at -O3 seemed to box a float in one call only, and a
           Start then Stop read 2 minor words (ASSUMPTIONS 215b). *)
        let measure = Sys.opaque_identity (fun extra -> reading (Gc.minor_words ()) extra) in
        if o.is_start c then begin
          let m = Gc.minor_words () in
          ignore (Sys.opaque_identity (measure (Sys.opaque_identity 0.)));
          let extra = Sys.opaque_identity (Gc.minor_words () -. m) in
          Gc.compact ();
          measure extra
        end
        else reading entered 0.
    | Exec (most, jobs) ->
        let pair v = let n, x = o.un_pair v in (to_string n, to_string x) in
        let job v = let p, a, e, d, i = o.un_job v in (to_string p, strs a, items pair e, Option.map to_string (o.un_some d), to_string i) in
        let jobs = items job jobs in
        let refuse why = List.map (fun (prog, _, _, _, _) -> Error (prog ^ ": " ^ why)) jobs in
        let most = Option.map to_z (o.un_some most) in
        let rs =
          if jobs = [] then []
          else if not w.exec then refuse "exec is disabled (--no-exec)"
          else if not (reaches !(w.fence) Write []) then refuse "exec needs the whole filesystem writable, which the fence does not allow"
          else if most = Some Z.zero then refuse "max-parallel is 0"
          else
            match exec_all (match most with Some z -> Option.value (clamp z) ~default:max_int | None -> Lazy.force processors) jobs with
            | rs -> rs
            | exception ((Unix.Unix_error _ | Sys_error _) as e) -> refuse (explain e)
        in
        o.exec_results
          (list (function Ok (code, out, err) -> o.ok (o.apply o.mk_exited [ o.u8 (nat code); of_string out; of_string err ]) | Error m -> o.fail (of_string m)) rs)
  in
  let run_program _w v =
    ignore (Lazy.force started);
    let rec loop v = match o.step v with Exit code -> u8 code | Continue k -> loop (o.apply k []) in
    try loop v with Halt code -> code
  in
  let run_main w f = let s, i, n = to_slice (o.apply f [ of_string (w.read_rest ()) ]) in if spend w n then w.out s i n else w.exit 1 in
  { of_string; to_string; perform; run_program; run_main }
end
open Ffi_core.Cast
let absurd () = prerr_endline "runtime error: absurd code reached"; exit 1
type yes = Yes_ and no = No_
let m_plain : Obj.t = to_any (fun (v : Obj.t) : Obj.t -> v)
let des_Nat v = to_any (Ffi_core.nat_view ~z:of_any ~nat:to_any v)
let con_Nat v = Ffi_core.nat_of ~z:of_any ~nat:to_any (of_any v)
let des_Half v = to_any (Ffi_core.half_view ~z:of_any ~nat:to_any v)
let con_Half v = Ffi_core.half_of ~z:of_any ~nat:to_any (of_any v)
let des_String v = to_any (Ffi_core.str_view ~slice:of_any ~u8:to_any ~str:to_any v)
let con_String v = Ffi_core.str_of ~z:of_any ~slice:of_any ~str:to_any (of_any v)
let des_Array v = to_any (Ffi_core.array_view ~array:of_any ~wrap:to_any v)
let con_Array v = Ffi_core.array_of ~array:of_any ~wrap:to_any (of_any v)
let des_Slots v = to_any (Ffi_core.slots_view ~slots:of_any ~list:to_any v)
let con_Slots v = Ffi_core.slots_of ~list:of_any ~wrap:to_any (of_any v)
let des_Bytes v = to_any (Ffi_core.bytes_view ~bytes:of_any ~u8:to_any ~wrap:to_any v)
let con_Bytes v = Ffi_core.bytes_of ~z:of_any ~bytes:of_any ~wrap:to_any (of_any v)
let des_Raw v = to_any (Ffi_core.raw_view ~handle:to_any ~symbol:to_any ~get:of_any ~str:(fun s -> to_any ((s, 0, String.length s) : Ffi_core.slice)) ~nat:to_any ~pos:to_any ~list:to_any ~raw:to_any v)
let con_Raw v = to_any (Ffi_core.raw_of ~unhandle:(fun l h -> let x, r, m, v = (of_any h : int * Ffi_core.reading * Ffi_core.mult * Obj.t) in Ffi_core.Handle (l, x, r, m, v)) ~unsymbol:of_any ~text:(fun v -> let (s, o, l) = (of_any v : Ffi_core.slice) in String.sub s o l) ~z:of_any ~pos:of_any ~list:of_any ~raw:of_any (of_any v))
let show_any (v : Obj.t) : string = "?"
let flush_to oc s o l = output_substring oc s o l; flush oc
let print_final = print_endline
let world = { Driver_core.read_rest = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin); out = flush_to stdout; err = flush_to stderr; args = List.tl (Array.to_list Sys.argv); env = Sys.getenv_opt; envs = Driver_core.host_envs; cwd = Sys.getcwd; exit; print = print_endline; exec = true; fence = ref Driver_core.unconfined; limit = ref None; used = ref 0 }
type t0 = K0_0 | K0_1 of { mutable f0 : Obj.t; mutable f1 : Obj.t }
and t1 = K1_0 | K1_1 of { mutable f0 : Obj.t }
and t2 = K2_0 of { mutable f0 : Obj.t } | K2_1 of { mutable f0 : Obj.t }
and t3 = K3_0 of { mutable f0 : Obj.t } | K3_1 of { mutable f0 : Obj.t } | K3_2 | K3_3 of { mutable f0 : Obj.t } | K3_4 of { mutable f0 : Obj.t; mutable f1 : Obj.t } | K3_5 of { mutable f0 : Obj.t; mutable f1 : Obj.t } | K3_6 | K3_7 of { mutable f0 : Obj.t } | K3_8 | K3_9 of { mutable f0 : Obj.t; mutable f1 : Obj.t } | K3_10 | K3_11 of { mutable f0 : Obj.t } | K3_12 | K3_13 of { mutable f0 : Obj.t } | K3_14 of { mutable f0 : Obj.t } | K3_15 of { mutable f0 : Obj.t } | K3_16 of { mutable f0 : Obj.t } | K3_17 of { mutable f0 : Obj.t; mutable f1 : Obj.t } | K3_18 of { mutable f0 : Obj.t } | K3_19 of { mutable f0 : Obj.t } | K3_20 of { mutable f0 : Obj.t; mutable f1 : Obj.t }
and t4 = K4_0 | K4_1
and t5 = K5_0 of { mutable f0 : Obj.t; mutable f1 : Obj.t }
and t6 = K6_0 | K6_1 | K6_2 | K6_3
and t7 = K7_0
and t8 = K8_0 of { mutable f0 : Obj.t; mutable f1 : Obj.t; mutable f2 : Obj.t; mutable f3 : Obj.t; mutable f4 : Obj.t; mutable f5 : Obj.t; mutable f6 : Obj.t; mutable f7 : Obj.t }
and t9 = K9_0 of { mutable f0 : Obj.t; mutable f1 : Obj.t; mutable f2 : Obj.t }
and t10 = K10_0 of { mutable f0 : Obj.t; mutable f1 : Obj.t; mutable f2 : Obj.t; mutable f3 : Obj.t; mutable f4 : Obj.t }
let driver = Driver_core.make ~str_of_host:(fun s -> to_any ((s, 0, String.length s) : Ffi_core.slice)) ~str_to_slice:(fun v -> (of_any v : Ffi_core.slice)) ~nat_to_z:(fun v -> (of_any v : Z.t)) ~nat_of_z:to_any { Driver_core.zero = ( to_any Z.zero); Driver_core.succ = (fun (f0 : Obj.t) -> ( (if Obj.is_int f0 && (of_any f0 : int) < max_int then to_any ((of_any f0 : int) + 1) else to_any (Z.succ (of_any f0 : Z.t))))); Driver_core.pred = (fun (v : Obj.t) -> ( if (of_any v : Z.t) == Z.zero then None else let f0 = (if Obj.is_int v then to_any ((of_any v : int) - 1) else to_any (Z.pred (of_any v : Z.t))) in (Some (f0)))); Driver_core.u8 = (fun (f0 : Obj.t) -> f0); Driver_core.un_u8 = (fun (v : Obj.t) -> (let f0 = v in f0)); Driver_core.char = (fun (f0 : Obj.t) -> f0); Driver_core.un_char = (fun (v : Obj.t) -> (let f0 = v in f0)); Driver_core.snil = ( to_any (("", 0, 0) : Ffi_core.slice)); Driver_core.scons = (fun (f0 : Obj.t) (f1 : Obj.t) -> ( let (x0_t0, x0_t1, x0_t2) = (of_any f1 : Ffi_core.slice) in to_any ((String.make 1 (Char.chr (Z.to_int (of_any f0 : Z.t))) ^ String.sub x0_t0 x0_t1 x0_t2, 0, x0_t2 + 1) : Ffi_core.slice))); Driver_core.un_str = (fun (v : Obj.t) -> ( let (x0_t0, x0_t1, x0_t2) = (of_any v : Ffi_core.slice) in if x0_t2 = 0 then None else let f0 = to_any (Z.of_int (Char.code (String.unsafe_get x0_t0 x0_t1))) and f1 = to_any ((x0_t0, x0_t1 + 1, x0_t2 - 1) : Ffi_core.slice) in (Some (f0, f1)))); Driver_core.un_list = (fun (v : Obj.t) -> (match (of_any v : t0) with | K0_0 -> None | K0_1 { f0 = f0; f1 = f1 } -> (Some (f0, f1)) )); Driver_core.un_pair = (fun (v : Obj.t) -> (match (of_any v : t5) with K5_0 { f0 = f0; f1 = f1 } -> (f0, f1))); Driver_core.un_some = (fun (v : Obj.t) -> (match (of_any v : t1) with | K1_0 -> None | K1_1 { f0 = f0 } -> (Some (f0)) )); Driver_core.some = (fun (f0 : Obj.t) -> (to_any (K1_1 { f0 = f0 }))); Driver_core.none = (to_any (K1_0)); Driver_core.ok = (fun (f0 : Obj.t) -> (to_any (K2_0 { f0 = f0 }))); Driver_core.fail = (fun (f0 : Obj.t) -> (to_any (K2_1 { f0 = f0 }))); Driver_core.unit = (to_any (K7_0)); Driver_core.cons = (fun (f0 : Obj.t) (f1 : Obj.t) -> (to_any (K0_1 { f0 = f0; f1 = f1 }))); Driver_core.nil = (to_any (K0_0)); Driver_core.pair = (fun (f0 : Obj.t) (f1 : Obj.t) -> (to_any (K5_0 { f0 = f0; f1 = f1 }))); Driver_core.is_file = (to_any (K6_0)); Driver_core.is_dir = (to_any (K6_1)); Driver_core.is_other = (to_any (K6_2)); Driver_core.missing = (to_any (K6_3)); Driver_core.changed = (to_any (K4_0)); Driver_core.unchanged = (to_any (K4_1)); Driver_core.mk_usage = (to_any (fun (f0 : Obj.t) (f1 : Obj.t) (f2 : Obj.t) (f3 : Obj.t) (f4 : Obj.t) (f5 : Obj.t) (f6 : Obj.t) (f7 : Obj.t) -> (to_any (K8_0 { f0 = f0; f1 = f1; f2 = f2; f3 = f3; f4 = f4; f5 = f5; f6 = f6; f7 = f7 })))); Driver_core.mk_exited = (to_any (fun (f0 : Obj.t) (f1 : Obj.t) (f2 : Obj.t) -> (to_any (K9_0 { f0 = f0; f1 = f1; f2 = f2 })))); Driver_core.un_job = (fun (v : Obj.t) -> (match (of_any v : t10) with K10_0 { f0 = f0; f1 = f1; f2 = f2; f3 = f3; f4 = f4 } -> (f0, f1, f2, f3, f4))); Driver_core.exec_results = (fun (f0 : Obj.t) -> f0); Driver_core.request = (fun (v : Obj.t) -> (match (of_any v : t3) with | K3_0 { f0 = f0 } -> (Driver_core.WriteOut (f0)) | K3_1 { f0 = f0 } -> (Driver_core.WriteErr (f0)) | K3_2 -> (Driver_core.ReadLine) | K3_3 { f0 = f0 } -> (Driver_core.ReadFile (f0)) | K3_4 { f0 = f0; f1 = f1 } -> (Driver_core.ReadFileIn (f0, f1)) | K3_5 { f0 = f0; f1 = f1 } -> (Driver_core.WriteFile (f0, f1)) | K3_6 -> (Driver_core.GetArgs) | K3_7 { f0 = f0 } -> (Driver_core.GetEnv (f0)) | K3_8 -> (Driver_core.GetEnvs) | K3_9 { f0 = f0; f1 = f1 } -> (Driver_core.AppendFile (f0, f1)) | K3_10 -> (Driver_core.ReadRemaining) | K3_11 { f0 = f0 } -> (Driver_core.ListDir (f0)) | K3_12 -> (Driver_core.GetCwd) | K3_13 { f0 = f0 } -> (Driver_core.Stat (f0)) | K3_14 { f0 = f0 } -> (Driver_core.MkDir (f0)) | K3_15 { f0 = f0 } -> (Driver_core.DeleteFile (f0)) | K3_16 { f0 = f0 } -> (Driver_core.DeleteDir (f0)) | K3_17 { f0 = f0; f1 = f1 } -> (Driver_core.ConfinePaths (f0, f1)) | K3_18 { f0 = f0 } -> (Driver_core.ConfineOutputBytes (f0)) | K3_19 { f0 = f0 } -> (Driver_core.Measure (f0)) | K3_20 { f0 = f0; f1 = f1 } -> (Driver_core.Exec (f0, f1)) )); Driver_core.step = (fun (v : Obj.t) -> (match (of_any v : t2) with | K2_0 { f0 = f0 } -> (Driver_core.Exit (f0)) | K2_1 { f0 = f0 } -> (Driver_core.Continue (f0)) )); Driver_core.is_start = (fun (v : Obj.t) -> (match (of_any v : t4) with | K4_0 -> true | K4_1 -> false )); Driver_core.apply = (fun (k : Obj.t) xs -> if xs = [] then (of_any k : unit -> Obj.t) () else List.fold_left (fun f (x : Obj.t) -> (of_any f : Obj.t -> Obj.t) x) k xs) }
let world = Driver_core.start [] [] None true true world
let print_final = Driver_core.print world
let a4 : Obj.t = (to_any ())
let a215 : Obj.t = (to_any (fun () -> ( to_any Z.zero)))
let a948 : Obj.t = (to_any (fun (f0 : Obj.t) (f1 : Obj.t) -> (to_any (K5_0 { f0 = f0; f1 = f1 }))))
let a1568 : Obj.t = (to_any (fun (f0 : Obj.t) (f1 : Obj.t) -> (to_any (K5_0 { f0 = f0; f1 = f1 }))))
let rec v42466_swap_in_a1571 (v42468_t : Obj.t) (v42470_z : Obj.t) : Obj.t = (match (of_any v42468_t : t5) with K5_0 { f0 = v42474_x; f1 = v42476_y } -> (let v42592___42592__ = (let cell3 = v42468_t in Array.unsafe_set (of_any cell3 : int array) 0 (of_any v42476_y : int); Array.unsafe_set (of_any cell3 : int array) 1 (of_any v42470_z : int); cell3) in (to_any ())))
let a1572 : Obj.t = (to_any v42466_swap_in_a1571)
let rec v42601_write_in_a1574 (v42603_t : Obj.t) (v42605_z : Obj.t) : Obj.t = (match (of_any v42603_t : t5) with K5_0 { f0 = v42609_x; f1 = v42611_y } -> (let v42683___42683__ = (let cell3 = v42603_t in Array.unsafe_set (of_any cell3 : int array) 0 (of_any v42605_z : int); cell3) in (to_any ())))
let a1575 : Obj.t = (to_any v42601_write_in_a1574)
let rec v42690_fresh_in_a1577 (v42692_z : Obj.t) : Obj.t = (let v42696_u = (to_any (K5_0 { f0 = a4; f1 = a4 })) in (let cell3 = v42696_u in Array.unsafe_set (of_any cell3 : int array) 0 (of_any v42692_z : int); Array.unsafe_set (of_any cell3 : int array) 1 (of_any v42692_z : int); cell3))
let a1578 : Obj.t = (to_any v42690_fresh_in_a1577)
let rec v42765_char_u62_a1580 (v42767_c : Obj.t) : Obj.t = v42767_c
let a1581 : Obj.t = (to_any v42765_char_u62_a1580)
let a1585 : Obj.t = (to_any 1)
let a1589 : Obj.t = (to_any 2)
let rec v42874_main_a1591 () : Obj.t = (let v42882_one = (v42765_char_u62_a1580 a1585) in (let v42890_two = (v42765_char_u62_a1580 a1589) in (let v42900___42900__ = ( to_any Z.zero) in (let v42904_t = (to_any (K5_0 { f0 = v42882_one; f1 = v42900___42900__ })) in (let _ = (v42466_swap_in_a1571 v42904_t v42882_one) in (let _ = (v42601_write_in_a1574 v42904_t v42890_two) in (let v42940___42940__ = (v42690_fresh_in_a1577 v42890_two) in (to_any (K5_0 { f0 = v42904_t; f1 = v42940___42940__ })))))))))
let a1592 : Obj.t = (to_any v42874_main_a1591)
let rec show_3 (v : Obj.t) : string = (Z.to_string (of_any v : Z.t))
and show_2 (v : Obj.t) : string = (let f0 = v in (Ffi_core.show_app "MkU62" [ show_3 f0; "_" ]))
and show_1 (v : Obj.t) : string = (match (of_any v : t5) with K5_0 { f0 = f0; f1 = f1 } -> (Ffi_core.show_app "MkTwo" [ show_2 f0; show_2 f1 ]))
and show_0 (v : Obj.t) : string = (match (of_any v : t5) with K5_0 { f0 = f0; f1 = f1 } -> (Ffi_core.show_app "MkPair" [ "_"; "_"; show_1 f0; show_1 f1 ]))
let () = print_final (show_0 ((of_any a1592 : unit -> Obj.t) ()))
