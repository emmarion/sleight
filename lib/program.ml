(* Runs a program's final value against a [world] (DESIGN.md section 27), which the test runner stands in for. *)
open Term
module V = Value
include Driver_core

let prelude_opt env name = Env.lookup { env with Env.scope = env.Env.prelude } name
let prelude env name = Option.get (prelude_opt env name)
let ctor env name = match (Env.entry env (prelude env name)).state with Env.Const (V.VCtorFn c) -> c | _ -> assert false

type final = Main | Io | Thunk of term | Plain

let final env ty =
  let string t = Option.fold ~none:false ~some:(fun s -> equal t (App (Var s, []))) (prelude_opt env "String") in
  let ret ps r = let env, ids = Elab.open_tele env ps in Env.canon env (fst (Elab.fact_of env Reader.nowhere (map_sg (instantiate (List.rev_map (fun x -> Var x) ids)) r.sg))) in
  match Env.canon env ty with
  | Fn (_, ([ { mult = Many; sg = Ty a; _ } ] as ps), [ ({ mult = Many; _ } as r) ]) when string a && string (ret ps r) -> Main
  | App (Var t, [ _ ]) when Some t = prelude_opt env "IO" -> Io
  | Fn (_, [], [ ({ mult = Many | Unique; _ } as r) ]) -> Thunk (ret [] r)
  | _ -> Plain

let driver env =
  let c = ctor env in
  let build n args = V.construct (c n) args and des n v = V.destruct (c n) v in
  let one n v = match des n v with _, [ x ] -> x | _ -> assert false in
  let request v =
    let i, fs = des "Exit" v in
    match ((V.ctor_at (c "Exit").adt i).cname, fs) with
    | "Exit", [ x ] -> Exit x
    | "Step", [ k ] -> Step k
    | "WriteOut", [ s; k ] -> WriteOut (s, k)
    | "WriteErr", [ s; k ] -> WriteErr (s, k)
    | "ReadLine", [ k ] -> ReadLine k
    | "ReadFile", [ p; k ] -> ReadFile (p, k)
    | "WriteFile", [ p; s; k ] -> WriteFile (p, s, k)
    | "GetArgs", [ k ] -> GetArgs k
    | "GetEnv", [ n; k ] -> GetEnv (n, k)
    | "GetEnvs", [ k ] -> GetEnvs k
    | "AppendFile", [ p; s; k ] -> AppendFile (p, s, k)
    | "ReadRemaining", [ k ] -> ReadRemaining k
    | "ListDir", [ p; k ] -> ListDir (p, k)
    | "GetCwd", [ k ] -> GetCwd k
    | "Stat", [ p; k ] -> Stat (p, k)
    | "MkDir", [ p; k ] -> MkDir (p, k)
    | "DeleteFile", [ p; k ] -> DeleteFile (p, k)
    | "DeleteDir", [ p; k ] -> DeleteDir (p, k)
    | "ConfineDir", [ p; k ] -> ConfineDir (p, k)
    | "ConfineOutputBytes", [ n; k ] -> ConfineOutputBytes (n, k)
    | _ -> assert false
  in
  let slice = !V.use_externs && Hashtbl.mem Ffi.registered "String" in
  let str_of_host = if slice then Some (fun s -> Ffi.text (s, 0, String.length s)) else None in
  let str_to_host = if slice then Some (fun v -> let s, o, l = Ffi.slice v in String.sub s o l) else None in
  let nat_to_z = if !V.use_externs && Hashtbl.mem Ffi.registered "Nat" then Some Ffi.z else None in
  make ?str_of_host ?str_to_host ?nat_to_z
    { zero = build "Zero" []; succ = (fun n -> build "Succ" [ n ]); pred = (fun v -> match des "Zero" v with 1, [ p ] -> Some p | _ -> None);
      u8 = (fun n -> build "MkU8" [ n ]); un_u8 = one "MkU8"; char = (fun n -> build "MkChar" [ n ]); un_char = one "MkChar";
      snil = build "SNil" []; scons = (fun ch r -> build "SCons" [ ch; r ]); un_str = (fun v -> match des "SNil" v with 1, [ ch; r ] -> Some (ch, r) | _ -> None);
      some = (fun x -> build "Some" [ x ]); none = build "None" []; ok = (fun x -> build "Ok" [ x ]); fail = (fun x -> build "Fail" [ x ]); unit = build "MkUnit" [];
      cons = (fun a b -> build "Cons" [ a; b ]); nil = build "Nil" []; pair = (fun a b -> build "MkPair" [ a; b ]);
      is_file = build "IsFile" []; is_dir = build "IsDir" []; is_other = build "IsOther" []; missing = build "Missing" [];
      changed = build "Changed" []; unchanged = build "Unchanged" [];
      request; apply = (fun k x -> List.hd (Eval.apply k [ x ])); apply0 = (fun k -> List.hd (Eval.apply k [])) }

(* A message names where it is about, the file the location carries or, where it carries none, the file
   being read. A contradiction that reaches here escaped every form that would have placed it, and the
   evaluator's code has no locations at all (ASSUMPTIONS 194). *)
let explain path = function
  | Reader.Syntax (l, m) -> Some (Reader.where path l ^ ": syntax error: " ^ m)
  | Env.Error (l, m) -> let here = Reader.where path l in Some (Env.resolve here (here ^ ": error: " ^ m))
  | Env.Contradiction m -> Some (Env.resolve path (path ^ ": error: contradiction: " ^ Lazy.force m))
  | Eval.Runtime m -> Some (path ^ ": runtime error: " ^ m)
  | _ -> None

let adapt_final env ty v =
  match final env ty, Env.canon env ty with
  | (Main | Thunk _), Fn (_, ps, [ { place = Some p; _ } ]) ->
      let ids = List.map (fun _ -> Env.fresh ()) ps in
      let p = instantiate (List.rev_map (fun x -> Var x) ids) p in
      let source = match p with SlotOf (Var x) when List.mem x ids -> V.CVar x | _ -> V.CVar (Elab.location_var env Reader.nowhere p) in
      let passed = Elab.runtime_ids ps ids in
      let fn = { V.fname = "at-final"; params = passed;
        body = V.CLet ([], V.CApp (V.CConst v, List.map (fun x -> V.CVar x) passed, V.Plain), source); impl = None } in
      V.VFn { fn; env = lazy env.Env.values }
  | _ -> v

let consume w env ty v =
  let v = adapt_final env ty v in
  match final env ty with
  | Main -> (driver env).run_main w v
  | Io -> w.exit ((driver env).run_io w v)
  | Thunk t -> print w (Elab.show_value env Reader.nowhere t (List.hd (Eval.apply v [])))
  | Plain -> print w (Elab.show_value env Reader.nowhere ty v)
