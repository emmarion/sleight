type slice = string * int * int

(* A Peano-declared type held as an integer: constructor 0 is zero, constructor 1 the successor. *)
let peano ~z ~nat =
  ( (fun i args -> match (i, args) with 0, [] -> nat Z.zero | 1, [ n ] -> nat (Z.succ (z n)) | _ -> assert false),
    fun v -> let n = z v in if Z.equal n Z.zero then (0, []) else (1, [ nat (Z.pred n) ]) )

(* Bijective base 2 held as an integer: constructor 1 is 2b+1, constructor 2 is 2b+2, so every integer has one spelling. *)
let bijective ~z ~bin =
  let digit d b = bin (Z.add (Z.shift_left (z b) 1) (Z.of_int d)) in
  ( (fun i args -> match (i, args) with 0, [] -> bin Z.zero | (1 | 2), [ b ] -> digit i b | _ -> assert false),
    fun v ->
      let n = z v in
      if Z.equal n Z.zero then (0, [])
      else let d = if Z.is_odd n then 1 else 2 in (d, [ bin (Z.shift_right (Z.sub n (Z.of_int d)) 1) ]) )

(* A cons list of Char held as a slice of a byte string: destructing yields the tail slice over the same buffer. *)
let text ~z ~slice ~u8 ~str =
  ( (fun i args ->
      match (i, args) with
      | 0, [] -> str ("", 0, 0)
      | 1, [ c; rest ] ->
          let s, o, l = slice rest in
          str (String.make 1 (Char.chr (Z.to_int (z c))) ^ String.sub s o l, 0, l + 1)
      | _ -> assert false),
    fun v -> let s, o, l = slice v in if l = 0 then (0, []) else (1, [ u8 (Z.of_int (Char.code s.[o])); str (s, o + 1, l - 1) ]) )

(* A type whose values are their constructor index alone, every field erased. *)
let indexed ~z ~mk = ((fun i _ -> mk (Z.of_int i)), fun v -> (Z.to_int (z v), []))

let add = Z.add
let nat_cmp a b = Z.of_int (if Z.lt a b then 0 else if Z.equal a b then 1 else 2)
let nat_mod = Z.rem
let bin_to_nat n = n
let trim (s, o, l) = (String.sub s o l, 0, l)
let append (s1, o1, l1) (s2, o2, l2) = (String.sub s1 o1 l1 ^ String.sub s2 o2 l2, 0, l1 + l2)

(* A rope (constructors 0 empty, 1 a string, 2 a pair, 3 a character) flattened in two passes: its leaves in
   order, then one buffer of their total length. [des] takes a value apart, [slice] and [z] read the two kinds of
   leaf, [str] makes the result. *)
let flatten ~des ~slice ~z ~str root =
  let rec leaves acc = function
    | [] -> acc
    | v :: rest -> (
        match des v with
        | 0, [] -> leaves acc rest
        | 1, [ s ] -> leaves (slice s :: acc) rest
        | 2, [ a; b ] -> leaves acc (a :: b :: rest)
        | 3, [ c ] -> leaves ((String.make 1 (Char.chr (Z.to_int (z c))), 0, 1) :: acc) rest
        | _ -> assert false)
  in
  let ls = List.rev (leaves [] [ root ]) in
  let total = List.fold_left (fun n (_, _, l) -> n + l) 0 ls in
  let buf = Bytes.create total in
  ignore (List.fold_left (fun pos (s, o, l) -> Bytes.blit_string s o buf pos l; pos + l) 0 ls);
  str (Bytes.unsafe_to_string buf, 0, total)
