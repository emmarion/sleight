let absurd () = prerr_endline "runtime error: absurd code reached"; exit 1
type yes = Yes_ and no = No_
let m_plain : Obj.t = to_any (fun (v : Obj.t) : Obj.t -> v)
let des_Nat v = to_any (Ffi_core.nat_view ~z:of_any ~nat:to_any v)
let con_Nat v = Ffi_core.nat_of ~z:of_any ~nat:to_any (of_any v)
let des_Half v = to_any (Ffi_core.half_view ~z:of_any ~nat:to_any v)
let con_Half v = Ffi_core.half_of ~z:of_any ~nat:to_any (of_any v)
let des_String v = to_any (Ffi_core.str_view ~slice:of_any ~u8:to_any ~str:to_any v)
let con_String v = Ffi_core.str_of ~z:of_any ~slice:of_any ~str:to_any (of_any v)
let des_Array v = to_any (Ffi_core.array_view ~array:of_any ~wrap:to_any v)
let con_Array v = Ffi_core.array_of ~array:of_any ~wrap:to_any (of_any v)
let des_Slots v = to_any (Ffi_core.slots_view ~slots:of_any ~list:to_any v)
let con_Slots v = Ffi_core.slots_of ~list:of_any ~wrap:to_any (of_any v)
let des_Bytes v = to_any (Ffi_core.bytes_view ~bytes:of_any ~u8:to_any ~wrap:to_any v)
let con_Bytes v = Ffi_core.bytes_of ~z:of_any ~bytes:of_any ~wrap:to_any (of_any v)
let des_Raw v = to_any (Ffi_core.raw_view ~handle:to_any ~symbol:to_any ~get:of_any ~str:(fun s -> to_any ((s, 0, String.length s) : Ffi_core.slice)) ~nat:to_any ~pos:to_any ~list:to_any ~raw:to_any v)
let con_Raw v = to_any (Ffi_core.raw_of ~unhandle:(fun l h -> let x, r, m, v = (of_any h : int * Ffi_core.reading * Ffi_core.mult * Obj.t) in Ffi_core.Handle (l, x, r, m, v)) ~unsymbol:of_any ~text:(fun v -> let (s, o, l) = (of_any v : Ffi_core.slice) in String.sub s o l) ~z:of_any ~pos:of_any ~list:of_any ~raw:of_any (of_any v))
let show_any (v : Obj.t) : string = "?"
let flush_to oc s o l = output_substring oc s o l; flush oc
let print_final = print_endline
let world = { Driver_core.read_rest = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin); out = flush_to stdout; err = flush_to stderr; args = List.tl (Array.to_list Sys.argv); env = Sys.getenv_opt; envs = Driver_core.host_envs; cwd = Sys.getcwd; exit; print = print_endline; exec = true; fence = ref Driver_core.unconfined; limit = ref None; used = ref 0 }
