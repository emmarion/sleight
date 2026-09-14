let absurd () = prerr_endline "runtime error: absurd code reached"; exit 1
type yes = Yes_ and no = No_
let m_plain : Obj.t = Obj.repr (fun (v : Obj.t) : Obj.t -> v)
let con_Nat, des_Nat = Ffi_core.peano ~z:Obj.obj ~nat:Obj.repr
let con_Bin, des_Bin = Ffi_core.bijective ~z:Obj.obj ~bin:Obj.repr
let con_String, des_String = Ffi_core.text ~z:Obj.obj ~slice:Obj.obj ~u8:Obj.repr ~str:Obj.repr
let show_any (v : Obj.t) : string = "?"
let flush_to oc s = output_string oc s; flush oc
let program_args = let rec go = function [] -> [] | "--" :: rest -> rest | _ :: rest -> go rest in go (Array.to_list Sys.argv)
let world = { Driver_core.input = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin); out = flush_to stdout; err = flush_to stderr; args = program_args; exit; print = print_endline }
