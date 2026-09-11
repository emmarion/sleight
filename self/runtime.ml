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
let member g i = match g with Tup fs -> List.nth fs i | f -> f
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
