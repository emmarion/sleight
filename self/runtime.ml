let absurd () = prerr_endline "runtime error: absurd code reached"; exit 1
type yes = Yes_ and no = No_
let m_plain : Obj.t = Obj.repr (fun (v : Obj.t) : Obj.t -> v)
let des_Nat v = Obj.repr (Ffi_core.nat_view ~z:Obj.obj ~nat:Obj.repr v)
let con_Nat v = Ffi_core.nat_of ~z:Obj.obj ~nat:Obj.repr (Obj.obj v)
let des_Half v = Obj.repr (Ffi_core.half_view ~z:Obj.obj ~nat:Obj.repr v)
let con_Half v = Ffi_core.half_of ~z:Obj.obj ~nat:Obj.repr (Obj.obj v)
let des_String v = Obj.repr (Ffi_core.str_view ~slice:Obj.obj ~u8:Obj.repr ~str:Obj.repr v)
let con_String v = Ffi_core.str_of ~z:Obj.obj ~slice:Obj.obj ~str:Obj.repr (Obj.obj v)
let show_any (v : Obj.t) : string = "?"
let flush_to oc s = output_string oc s; flush oc
let program_args = let rec go = function [] -> [] | "--" :: rest -> rest | _ :: rest -> go rest in go (Array.to_list Sys.argv)
let world = { Driver_core.read_rest = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin); out = flush_to stdout; err = flush_to stderr; args = program_args; env = Sys.getenv_opt; envs = Driver_core.host_envs; cwd = Sys.getcwd; exit; print = print_endline }
