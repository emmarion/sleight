let absurd () = prerr_endline "runtime error: absurd code reached"; exit 1
type yes = Yes_ and no = No_
let m_plain : Obj.t = Obj.repr (fun (v : Obj.t) : Obj.t -> v)
let des_Nat v = Obj.repr (Ffi_core.nat_view ~z:Obj.obj ~nat:Obj.repr v)
let con_Nat v = Ffi_core.nat_of ~z:Obj.obj ~nat:Obj.repr (Obj.obj v)
let des_Half v = Obj.repr (Ffi_core.half_view ~z:Obj.obj ~nat:Obj.repr v)
let con_Half v = Ffi_core.half_of ~z:Obj.obj ~nat:Obj.repr (Obj.obj v)
let des_String v = Obj.repr (Ffi_core.str_view ~slice:Obj.obj ~u8:Obj.repr ~str:Obj.repr v)
let con_String v = Ffi_core.str_of ~z:Obj.obj ~slice:Obj.obj ~str:Obj.repr (Obj.obj v)
let des_Array v = Obj.repr (Ffi_core.array_view ~array:Obj.obj ~wrap:Obj.repr v)
let con_Array v = Ffi_core.array_of ~array:Obj.obj ~wrap:Obj.repr (Obj.obj v)
let des_Bytes v = Obj.repr (Ffi_core.bytes_view ~bytes:Obj.obj ~u8:Obj.repr ~wrap:Obj.repr v)
let con_Bytes v = Ffi_core.bytes_of ~z:Obj.obj ~bytes:Obj.obj ~wrap:Obj.repr (Obj.obj v)
let des_Raw v = Obj.repr (Ffi_core.raw_view ~handle:Obj.repr ~get:Obj.obj ~str:(fun s -> Obj.repr ((s, 0, String.length s) : Ffi_core.slice)) ~nat:Obj.repr ~pos:Obj.repr ~list:Obj.repr ~raw:Obj.repr v)
let con_Raw v = Obj.repr (Ffi_core.raw_of ~unhandle:Obj.obj ~text:(fun v -> let (s, o, l) = (Obj.obj v : Ffi_core.slice) in String.sub s o l) ~z:Obj.obj ~pos:Obj.obj ~list:Obj.obj ~raw:Obj.obj (Obj.obj v))
let show_any (v : Obj.t) : string = "?"
let flush_to oc s = output_string oc s; flush oc
let print_final = print_endline
let world = { Driver_core.read_rest = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin); out = flush_to stdout; err = flush_to stderr; args = List.tl (Array.to_list Sys.argv); env = Sys.getenv_opt; envs = Driver_core.host_envs; cwd = Sys.getcwd; exit; print = print_endline; fence = ref "/"; limit = ref max_int; used = ref 0 }
