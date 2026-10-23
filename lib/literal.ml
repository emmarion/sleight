(* Literals are sugar over the prelude, interned where they are first met (DESIGN.md section 45, Elab.intern). *)

type t = Numeral of Z.t | Char of int | Str of string


let classify s =
  let n = String.length s in
  if n > 0 && String.for_all (fun c -> c >= '0' && c <= '9') s then
    if n > 1 && s.[0] = '0' then `Bad (s ^ " has a leading zero")
    else (match Ffi_core.nat_of_string s with Some z -> `Lit (Numeral z) | None -> assert false)
  else if n >= 2 && s.[0] = '"' then `Lit (Str (String.sub s 1 (n - 2)))
  else if n >= 2 && String.sub s 0 2 = "#\\" then
    match String.sub s 2 (n - 2) with
    | "space" -> `Lit (Char 32)
    | "newline" -> `Lit (Char 10)
    | "tab" -> `Lit (Char 9)
    | c when String.length c = 1 -> `Lit (Char (Char.code c.[0]))
    | c when String.length c = 3 && c.[0] = 'x' && String.for_all (function '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true | _ -> false) (String.sub c 1 2) -> `Lit (Char (int_of_string ("0" ^ c)))
    | _ -> `Bad ("malformed character literal " ^ s)
  else `Name

let char c = Printf.sprintf "#\\x%02x" c
let key = function Numeral z -> Z.to_string z | Char c -> char c | Str s -> Ffi_core.lit_string s

let plain s =
  s <> "_" && s <> "$" && s <> "" && s.[0] <> '"' && (not (String.starts_with ~prefix:"__" s)) && (not (String.starts_with ~prefix:"#\"" s))
  && String.for_all (fun c -> c > ' ' && c <= '~' && not (String.contains "();" c)) s && classify s = `Name

let spell_name s = if plain s then s else "#" ^ Ffi_core.lit_string s
let name : Ffi_core.name -> string = function Src s -> spell_name s | Gen (n, s) -> "__g" ^ Z.to_string n ^ "_" ^ spell_name s

(* The source spelling a literal reads back from, [classify]'s inverse: a numeral in decimal, a character bare
   where the reader's word syntax admits it, and a string escaped the way [Reader.files] unescapes. *)
let spell = function Numeral z -> Z.to_string z | Char c -> Ffi_core.lit_char c | Str s -> Ffi_core.lit_string s
