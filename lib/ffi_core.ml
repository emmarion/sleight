type slice = string * int * int

(* Each extern type one level deep, in the order and arities of its model's constructors: [_view] takes a host
   value apart into the constructor at the top and host values below, [_of] puts one together. *)
type 'v nat = Zero | Succ of 'v
type 'v bin = BZ | B1 of 'v | B2 of 'v
type 'v str = SNil | SCons of 'v * 'v
type 'v rope = REmpty | RStr of 'v | RCat of 'v * 'v | RChar of 'v
type cmp = CLt | CEq | CGt

let nat_view ~z ~nat v = let n = z v in if Z.equal n Z.zero then Zero else Succ (nat (Z.pred n))
let nat_of ~z ~nat = function Zero -> nat Z.zero | Succ p -> nat (Z.succ (z p))

(* Bijective base 2: B1 b is 2b+1, B2 b is 2b+2, so every integer has one spelling. *)
let bin_view ~z ~bin v =
  let n = z v in
  if Z.equal n Z.zero then BZ else let b = bin (Z.shift_right (Z.pred n) 1) in if Z.is_odd n then B1 b else B2 b
let bin_of ~z ~bin = function BZ -> bin Z.zero | B1 b -> bin (Z.succ (Z.shift_left (z b) 1)) | B2 b -> bin (Z.add (Z.shift_left (z b) 1) (Z.of_int 2))

(* A cons list of Char held as a slice of a byte string: the tail is a slice over the same buffer. *)
let str_view ~slice ~u8 ~str v = let s, o, l = slice v in if l = 0 then SNil else SCons (u8 (Z.of_int (Char.code s.[o])), str (s, o + 1, l - 1))
let str_of ~z ~slice ~str = function
  | SNil -> str ("", 0, 0)
  | SCons (c, rest) -> let s, o, l = slice rest in str (String.make 1 (Char.chr (Z.to_int (z c))) ^ String.sub s o l, 0, l + 1)

let add = Z.add
let sub = Z.sub
let mul = Z.mul
let div = Z.div
let divmod = Z.div_rem
let nat_cmp a b = if Z.lt a b then CLt else if Z.equal a b then CEq else CGt
let nat_mod = Z.rem
let bin_to_nat n = n
let trim (s, o, l) = (String.sub s o l, 0, l)
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
