(* Literals are sugar for run-position statements over the prelude, hoisted ahead of the top-level statement that
   first mentions them (ASSUMPTIONS.md). *)

type t = Numeral of Z.t | Char of int | Str of string

(* The reader hands a string literal over as an atom in this shape, which no name can take (section 28). *)
let quote s = "\"" ^ s ^ "\""

let classify s =
  let n = String.length s in
  if n > 0 && String.for_all (fun c -> c >= '0' && c <= '9') s then
    if n > 1 && s.[0] = '0' then `Bad (s ^ " has a leading zero") else `Lit (Numeral (Z.of_string s))
  else if n >= 2 && s.[0] = '"' then `Lit (Str (String.sub s 1 (n - 2)))
  else if n >= 2 && String.sub s 0 2 = "#\\" then
    match String.sub s 2 (n - 2) with
    | "space" -> `Lit (Char 32)
    | "newline" -> `Lit (Char 10)
    | "tab" -> `Lit (Char 9)
    | c when String.length c = 1 -> `Lit (Char (Char.code c.[0]))
    | c when String.length c = 3 && c.[0] = 'x' && int_of_string_opt ("0" ^ c) <> None -> `Lit (Char (int_of_string ("0" ^ c)))
    | _ -> `Bad ("malformed character literal " ^ s)
  else `Name

let char c = Printf.sprintf "#\\x%02x" c
let key = function Numeral z -> Z.to_string z | Char c -> char c | Str s -> quote s
let chars s = List.init (String.length s) (fun i -> Char (Char.code s.[i]))

(* The source spelling a literal reads back from, [classify]'s inverse: a numeral in decimal, a character bare
   where the reader's word syntax admits it, and a string escaped the way [Reader.tokenize] unescapes. *)
let spell = function Numeral z -> Z.to_string z | Char c -> Ffi_core.lit_char c | Str s -> Ffi_core.lit_string s

(* The bijective base-2 spelling of [z] as source: (B1 b) is 2b+1, (B2 b) is 2b+2. *)
let rec bin z = match Ffi_core.half_view ~z:Fun.id ~nat:Fun.id z with HZ -> "(BZ)" | H1 b -> "(B1 " ^ bin b ^ ")" | H2 b -> "(B2 " ^ bin b ^ ")"

let rec succs k base = if k <= 0 then base else succs (k - 1) (Printf.sprintf "(Succ %s)" base)

(* The witness that [z]'s spelling steps to [z+1]'s: (B1 x) steps to (B2 x), and (B2 x) to (B1 (succ x)). *)
let rec bin_succ z =
  match Ffi_core.half_view ~z:Fun.id ~nat:Fun.id z with
  | HZ -> "(BSZ)"
  | H1 x -> Printf.sprintf "(BS1 %s)" (bin x)
  | H2 x -> Printf.sprintf "(BS2 %s %s %s)" (bin x) (bin (Z.succ x)) (bin_succ x)

(* A numeral binds its Nat and Numeral proof; a character its Char, built by reflection on the decided bound
   (DESIGN.md section 41); a string its characters, each already a literal, consed up. *)
let source = function
  | Numeral z -> Printf.sprintf "(let (many _) (erased _) (bin-to-nat %s))" (bin z)
  | Char c -> Printf.sprintf "(let (many %%d) (lt-dec %d u8-modulus)) (comptime-match many %%d (Yes %%a %%b %%p)) (let (many _) (MkChar (MkU8 %d %%p)))" c c
  | Str s ->
      let cons c rest = Printf.sprintf "(SCons %s %s)" (char (Char.code c)) rest in
      "(let (many _) " ^ String.fold_right cons s "(SNil)" ^ ")"
