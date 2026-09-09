[@@@warning "-a"]
module Ffi_core = struct
type slice = string * int * int
let peano ~z ~nat =
  ( (fun i args -> match (i, args) with 0, [] -> nat Z.zero | 1, [ n ] -> nat (Z.succ (z n)) | _ -> assert false),
    fun v -> let n = z v in if Z.equal n Z.zero then (0, []) else (1, [ nat (Z.pred n) ]) )
let bijective ~z ~bin =
  let digit d b = bin (Z.add (Z.shift_left (z b) 1) (Z.of_int d)) in
  ( (fun i args -> match (i, args) with 0, [] -> bin Z.zero | (1 | 2), [ b ] -> digit i b | _ -> assert false),
    fun v ->
      let n = z v in
      if Z.equal n Z.zero then (0, [])
      else let d = if Z.is_odd n then 1 else 2 in (d, [ bin (Z.shift_right (Z.sub n (Z.of_int d)) 1) ]) )
let text ~z ~slice ~u8 ~str =
  ( (fun i args ->
      match (i, args) with
      | 0, [] -> str ("", 0, 0)
      | 1, [ c; rest ] ->
          let s, o, l = slice rest in
          str (String.make 1 (Char.chr (Z.to_int (z c))) ^ String.sub s o l, 0, l + 1)
      | _ -> assert false),
    fun v -> let s, o, l = slice v in if l = 0 then (0, []) else (1, [ u8 (Z.of_int (Char.code s.[o])); str (s, o + 1, l - 1) ]) )
let add = Z.add
let nat_cmp ~con a b = con (if Z.lt a b then 0 else if Z.equal a b then 1 else 2) []
let nat_mod = Z.rem
let bin_to_nat n = n
let trim (s, o, l) = (String.sub s o l, 0, l)
let append (s1, o1, l1) (s2, o2, l2) = (String.sub s1 o1 l1 ^ String.sub s2 o2 l2, 0, l1 + l2)

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

end
type v = Tag of int * v list | Tup of v list | Nat of Z.t | Str of Ffi_core.slice | Fn of (v list -> v) | Mat of (int -> v -> int * v list) | U
let absurd () = prerr_endline "runtime error: absurd code reached"; exit 1
let app f args = match f with Fn g -> g args | _ -> absurd ()
let app_mat m n v = match m with Mat f -> f n v | _ -> absurd ()
let z = function Nat n -> n | _ -> absurd ()
let slice = function Str s -> s | _ -> absurd ()
let nat n = Nat n
let (con_Nat : int -> v list -> v), (des_Nat : v -> int * v list) = Ffi_core.peano ~z ~nat
let (con_Bin : int -> v list -> v), (des_Bin : v -> int * v list) = Ffi_core.bijective ~z ~bin:nat
let (con_String : int -> v list -> v), (des_String : v -> int * v list) = Ffi_core.text ~z ~slice ~u8:nat ~str:(fun s -> Str s)
let tuple = function [] -> U | [ v ] -> v | vs -> Tup vs
let untuple n v = match (n, v) with 1, v -> [ v ] | 0, _ -> [] | _, Tup vs -> vs | _ -> absurd ()
let des_tag = function Tag (i, fs) -> (i, fs) | _ -> absurd ()
let ext_add = function [ a; b ] -> Nat (Ffi_core.add (z a) (z b)) | _ -> absurd ()
let ext_nat_cmp = function [ a; b ] -> Ffi_core.nat_cmp ~con:(fun i args -> Tag (i, args)) (z a) (z b) | _ -> absurd ()
let ext_nat_mod = function [ a; b ] -> Nat (Ffi_core.nat_mod (z a) (z b)) | _ -> absurd ()
let ext_bin_to_nat = function [ a ] -> Nat (Ffi_core.bin_to_nat (z a)) | _ -> absurd ()
let ext_trim = function [ a ] -> Str (Ffi_core.trim (slice a)) | _ -> absurd ()
let ext_append = function [ a; b ] -> Str (Ffi_core.append (slice a) (slice b)) | _ -> absurd ()
let ext_flatten = function [ r ] -> Ffi_core.flatten ~des:des_tag ~slice ~z ~str:(fun s -> Str s) r | _ -> absurd ()
let rec nat_of v = match des_Nat v with _, [ p ] -> 1 + nat_of p | _ -> 0
let of_string s = Str (s, 0, String.length s)
let to_string v =
  let buf = Buffer.create 64 in
  let rec go v = match des_String v with _, [ ch; rest ] -> Buffer.add_char buf (Char.chr (nat_of ch)); go rest | _ -> () in
  go v;
  Buffer.contents buf
let read_file path = In_channel.with_open_bin path In_channel.input_all
let write_file path s = Out_channel.with_open_bin path (fun oc -> Out_channel.output_string oc s)
let flush_to oc s = output_string oc s; flush oc
let program_args = let rec go = function [] -> [] | "--" :: rest -> rest | _ :: rest -> go rest in go (Array.to_list Sys.argv)
let run_io v =
  let result f = match f () with x -> Tag (0, [ x ]) | exception Sys_error m -> Tag (1, [ of_string m ]) in
  let rec loop v =
    match des_tag v with
    | 0, [ code ] -> nat_of code
    | 1, [ s; next ] -> flush_to stdout (to_string s); loop next
    | 2, [ s; next ] -> flush_to stderr (to_string s); loop next
    | 3, [ k ] -> loop (app k [ (match In_channel.input_line stdin with Some l -> Tag (1, [ of_string l ]) | None -> Tag (0, [])) ])
    | 4, [ path; k ] -> loop (app k [ result (fun () -> of_string (read_file (to_string path))) ])
    | 5, [ path; s; k ] -> loop (app k [ result (fun () -> write_file (to_string path) (to_string s); U) ])
    | 6, [ k ] -> loop (app k [ List.fold_right (fun a acc -> Tag (1, [ of_string a; acc ])) program_args (Tag (0, [])) ])
    | _ -> absurd ()
  in
  loop v
let run_main f = flush_to stdout (to_string (app f [ of_string (In_channel.input_all stdin) ]))
let rec show_any v =
  match v with
  | Tag (i, fs) -> "(#" ^ string_of_int i ^ String.concat "" (List.map (fun f -> " " ^ show_any f) fs) ^ ")"
  | Tup fs -> "(" ^ String.concat " " (List.map show_any fs) ^ ")"
  | Nat n -> Z.to_string n
  | Str (s, o, l) -> "\"" ^ String.escaped (String.sub s o l) ^ "\""
  | Fn _ -> "<function>"
  | Mat _ -> "<matchable>"
  | U -> "_"
