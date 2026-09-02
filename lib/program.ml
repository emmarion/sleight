(* The driver's reading of a program's final value (DESIGN.md section 16): a function from String to String is run
   over the input and its result written out; an IO value is interpreted request by request; a function from
   nothing to one value is applied and its result printed; anything else is printed. [world] is what the driver
   touches, so the test runner can stand one in. *)
open Term
module V = Value

type world = {
  input : unit -> string;
  read_line : unit -> string option;
  out : string -> unit;
  err : string -> unit;
  args : string list;
  exit : int -> unit;
  print : string -> unit;
}

let prelude env name = Option.get (Env.lookup { env with Env.scope = env.Env.prelude } name)
let ctor env name = match (Env.entry env (prelude env name)).state with Env.Const (V.VCtorFn c) -> c | _ -> assert false

type final = Main | Io | Thunk of term | Plain

let final env ty =
  let string = App (Var (prelude env "String"), []) in
  match Env.canon env ty with
  | Fn (_, [ { mult = Many; sg = Ty a; _ } ], [ { mult = Many; sg = Ty b; _ } ]) when equal a string && equal b string -> Main
  | App (Var t, [ _ ]) when t = prelude env "IO" -> Io
  | Fn (_, [], [ { mult = Many; sg = Ty t; _ } ]) -> Thunk t
  | _ -> Plain

let of_string env s =
  if !V.use_externs then Ffi.str s
  else
    let c = ctor env in
    let rec nat n = if n = 0 then V.construct (c "Zero") [] else V.construct (c "Succ") [ nat (n - 1) ] in
    let char b = V.construct (c "MkChar") [ V.construct (c "MkU8") [ nat b ] ] in
    String.fold_right (fun ch acc -> V.construct (c "SCons") [ char (Char.code ch); acc ]) s (V.construct (c "SNil") [])

let rec nat env v = match V.destruct (ctor env "Zero") v with _, [ p ] -> 1 + nat env p | _ -> 0
let u8 env v = match V.destruct (ctor env "MkU8") v with _, [ n ] -> nat env n | _ -> assert false

let to_string env v =
  let c = ctor env and buf = Buffer.create 64 in
  let rec go v =
    match V.destruct (c "SNil") v with
    | _, [ ch; rest ] -> Buffer.add_char buf (Char.chr (u8 env (List.hd (snd (V.destruct (c "MkChar") ch))))); go rest
    | _ -> ()
  in
  go v;
  Buffer.contents buf

let read_file path = In_channel.with_open_bin path In_channel.input_all
let explain path = function
  | Reader.Syntax (l, m) -> Some (Printf.sprintf "%s:%d: syntax error: %s" path l m)
  | Env.Error (l, m) -> Some (Printf.sprintf "%s:%d: error: %s" path l m)
  | Env.Contradiction m -> Some (path ^ ": error: contradiction: " ^ m)
  | Eval.Runtime m -> Some (path ^ ": runtime error: " ^ m)
  | _ -> None
let write_file path s = Out_channel.with_open_bin path (fun oc -> Out_channel.output_string oc s)

(* Interprets an IO value: performs each request, applies its continuation to the answer, and loops until Exit. *)
let run_io env w v =
  let c = ctor env in
  let str = of_string env and text = to_string env in
  let build name args = V.construct (c name) args in
  let result f = match f () with x -> build "Ok" [ x ] | exception Sys_error m -> build "Fail" [ str m ] in
  let step k x = List.hd (Eval.apply k [ x ]) in
  let rec loop v =
    let i, fields = V.destruct (c "Exit") v in
    match ((List.nth (c "Exit").adt.ctors i).cname, fields) with
    | "Exit", [ code ] -> u8 env code
    | "WriteOut", [ s; next ] -> w.out (text s); loop next
    | "WriteErr", [ s; next ] -> w.err (text s); loop next
    | "ReadLine", [ k ] -> loop (step k (match w.read_line () with Some l -> build "Some" [ str l ] | None -> build "None" []))
    | "ReadFile", [ path; k ] -> loop (step k (result (fun () -> str (read_file (text path)))))
    | "WriteFile", [ path; s; k ] -> loop (step k (result (fun () -> write_file (text path) (text s); build "MkUnit" [])))
    | "GetArgs", [ k ] -> loop (step k (List.fold_right (fun a acc -> build "Cons" [ str a; acc ]) w.args (build "Nil" [])))
    | _ -> assert false
  in
  loop v

let consume w env ty v =
  match final env ty with
  | Main -> w.out (to_string env (List.hd (Eval.apply v [ of_string env (w.input ()) ])))
  | Io -> w.exit (run_io env w v)
  | Thunk _ -> w.print (V.show (List.hd (Eval.apply v [])))
  | Plain -> w.print (V.show v)
