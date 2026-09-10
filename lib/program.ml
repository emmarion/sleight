(* Runs a program's final value against a [world] (DESIGN.md section 16), which the test runner stands in for. *)
open Term
module V = Value
include Driver_core

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

let driver env =
  let c = ctor env in
  make ~build:(fun n args -> V.construct (c n) args) ~des:(fun n v -> V.destruct (c n) v)
    ~io_name:(fun i -> (V.ctor_at (c "Exit").adt i).cname) ~apply:(fun k x -> List.hd (Eval.apply k [ x ]))
    ~str:(if !V.use_externs then Some Ffi.str else None)

let explain path = function
  | Reader.Syntax (l, m) -> Some (Printf.sprintf "%s:%d: syntax error: %s" path l m)
  | Env.Error (l, m) -> Some (Printf.sprintf "%s:%d: error: %s" path l m)
  | Env.Contradiction m -> Some (path ^ ": error: contradiction: " ^ m)
  | Eval.Runtime m -> Some (path ^ ": runtime error: " ^ m)
  | _ -> None

let consume w env ty v =
  match final env ty with
  | Main -> (driver env).run_main w v
  | Io -> w.exit ((driver env).run_io w v)
  | Thunk _ -> w.print (V.show (List.hd (Eval.apply v [])))
  | Plain -> w.print (V.show v)
