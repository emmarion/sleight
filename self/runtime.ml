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
let des_Slots v = Obj.repr (Ffi_core.slots_view ~slots:Obj.obj ~list:Obj.repr v)
let con_Slots v = Ffi_core.slots_of ~list:Obj.obj ~wrap:Obj.repr (Obj.obj v)
let des_Bytes v = Obj.repr (Ffi_core.bytes_view ~bytes:Obj.obj ~u8:Obj.repr ~wrap:Obj.repr v)
let con_Bytes v = Ffi_core.bytes_of ~z:Obj.obj ~bytes:Obj.obj ~wrap:Obj.repr (Obj.obj v)
let des_Raw v = Obj.repr (Ffi_core.raw_view ~handle:Obj.repr ~symbol:Obj.repr ~get:Obj.obj ~str:(fun s -> Obj.repr ((s, 0, String.length s) : Ffi_core.slice)) ~nat:Obj.repr ~pos:Obj.repr ~list:Obj.repr ~raw:Obj.repr v)
let con_Raw v = Obj.repr (Ffi_core.raw_of ~unhandle:(fun l h -> let x, r, m, v = (Obj.obj h : int * Ffi_core.reading * Ffi_core.mult * Obj.t) in Ffi_core.Handle (l, x, r, m, v)) ~unsymbol:Obj.obj ~text:(fun v -> let (s, o, l) = (Obj.obj v : Ffi_core.slice) in String.sub s o l) ~z:Obj.obj ~pos:Obj.obj ~list:Obj.obj ~raw:Obj.obj (Obj.obj v))
let show_any (v : Obj.t) : string = "?"
let flush_to oc s o l = output_substring oc s o l; flush oc
let print_final = print_endline
let world = { Driver_core.read_rest = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin); out = flush_to stdout; err = flush_to stderr; args = List.tl (Array.to_list Sys.argv); env = Sys.getenv_opt; envs = Driver_core.host_envs; cwd = Sys.getcwd; exit; print = print_endline; exec = true; fence = ref Driver_core.unconfined; limit = ref None; used = ref 0 }
let rt_data : Ffi_core.word array ref = ref [||]
let rt_next = ref 0
let rt_get k : Obj.t = Obj.magic (Array.unsafe_get !rt_data k)
let rt_push (v : Obj.t) = Array.unsafe_set !rt_data !rt_next (Obj.magic v : Ffi_core.word); incr rt_next
let rt_globals : Obj.t array ref = ref [||]
let rt_adapters : (Obj.t array -> Obj.t array) array ref = ref [||]
let rt_src = ref ""
let rt_pos = ref 0
let rt_num () =
  let s = !rt_src in
  let neg = s.[!rt_pos] = '-' in
  if neg then incr rt_pos;
  let n = ref 0 in
  while !rt_pos < String.length s && s.[!rt_pos] >= '0' && s.[!rt_pos] <= '9' do n := 10 * !n + Char.code s.[!rt_pos] - 48; incr rt_pos done;
  incr rt_pos;
  if neg then - !n else !n
let rt_ref () = if (!rt_src).[!rt_pos] = 'i' then (incr rt_pos; Obj.repr (rt_num ())) else rt_get (rt_num ())
let rt_text () = let n = rt_num () in let t = String.sub !rt_src !rt_pos n in rt_pos := !rt_pos + n + 1; t
let rt_run s =
  rt_src := s;
  rt_pos := 0;
  while !rt_pos < String.length s do
    let op = s.[!rt_pos] in
    incr rt_pos;
    match op with
    | 'b' -> let t = rt_num () in rt_push (Obj.new_block t (rt_num ()))
    | 't' -> ignore (rt_num ()); rt_push (Obj.repr (Ffi_core.slots_new ()))
    | 's' -> let t = rt_text () in rt_push (Obj.repr ((t, 0, String.length t) : Ffi_core.slice))
    | 'y' -> rt_push (Obj.repr (Bytes.of_string (rt_text ())))
    | 'z' -> rt_push (Obj.repr (Z.of_string (rt_text ())))
    | 'g' -> rt_push (!rt_globals).(rt_num ())
    | 'c' ->
        let a = rt_num () in
        let caps = Array.make (rt_num ()) (Obj.repr 0) in
        for i = 0 to Array.length caps - 1 do caps.(i) <- rt_ref () done;
        Array.iter rt_push ((!rt_adapters).(a) caps)
    | 'f' -> let b = rt_get (rt_num ()) in for i = 0 to rt_num () - 1 do Obj.set_field b i (rt_ref ()) done
    | 'k' -> let t = rt_get (rt_num ()) in for _ = 1 to rt_num () do ignore (Ffi_core.slots_add (Obj.obj t) (rt_ref ())) done
    | _ -> failwith "malformed data"
  done
