type slice = string * int * int

let modulus = Z.of_int 256

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

let nat_add = Z.add
let lt_dec a b = if Z.lt a b then Z.zero else Z.one
let u8_add a b = Z.rem (Z.add a b) modulus
let bin_to_nat n = n
let trim (s, o, l) = (String.sub s o l, 0, l)
