(* Runs a program's final value against a [world] (DESIGN.md section 27), which the test runner stands in for. *)
open Term
module V = Value
include Driver_core

let prelude_opt env name = Env.lookup { env with Env.scope = env.Env.prelude } (Reader.Src name)
let prelude env name = Option.get (prelude_opt env name)
let ctor env name = match (Env.entry env (prelude env name)).state with Env.Settled (V.VCtorFn c) -> c | _ -> assert false

type final = Elab.final = Main | Program | Thunk of term | Plain

let final = Elab.final

let driver env =
  let c = ctor env in
  let build n args = V.construct (c n) args and des n v = V.destruct (c n) v in
  let one n v = match des n v with _, [ x ] -> x | _ -> assert false in
  let request v =
    let i, fs = des "WriteOut" v in
    match ((V.ctor_at (c "WriteOut").adt i).cname, fs) with
    | "WriteOut", [ s ] -> WriteOut s
    | "WriteErr", [ s ] -> WriteErr s
    | "ReadLine", [] -> ReadLine
    | "ReadFile", [ p ] -> ReadFile p
    | "ReadFileIn", [ d; p ] -> ReadFileIn (d, p)
    | "WriteFile", [ p; s ] -> WriteFile (p, s)
    | "GetArgs", [] -> GetArgs
    | "GetEnv", [ n ] -> GetEnv n
    | "GetEnvs", [] -> GetEnvs
    | "AppendFile", [ p; s ] -> AppendFile (p, s)
    | "ReadRemaining", [] -> ReadRemaining
    | "ListDir", [ p ] -> ListDir p
    | "GetCwd", [] -> GetCwd
    | "Stat", [ p ] -> Stat p
    | "MkDir", [ p ] -> MkDir p
    | "DeleteFile", [ p ] -> DeleteFile p
    | "DeleteDir", [ p ] -> DeleteDir p
    | "ConfinePaths", [ r; w ] -> ConfinePaths (r, w)
    | "ConfineOutputBytes", [ n ] -> ConfineOutputBytes n
    | "Measure", [ m ] -> Measure m
    | "Exec", [ p; a; e; d; i ] -> Exec (p, a, e, d, i)
    | _ -> assert false
  in
  let step v = match des "Exit" v with 0, [ x ] -> Exit x | 1, [ k ] -> Continue k | _ -> assert false in
  let is_start v = fst (des "Start" v) = 0 in
  let slice = !V.use_externs && Hashtbl.mem Ffi.registered "String" in
  let str_of_host = if slice then Some (fun s -> Ffi.text (s, 0, String.length s)) else None in
  let str_to_host = if slice then Some (fun v -> let s, o, l = Ffi.slice v in String.sub s o l) else None in
  let ffi_nat = !V.use_externs && Hashtbl.mem Ffi.registered "Nat" in
  let nat_to_z = if ffi_nat then Some Ffi.z else None and nat_of_z = if ffi_nat then Some (Ffi.int "Nat") else None in
  make ?str_of_host ?str_to_host ?nat_to_z ?nat_of_z
    { zero = build "Zero" []; succ = (fun n -> build "Succ" [ n ]); pred = (fun v -> match des "Zero" v with 1, [ p ] -> Some p | _ -> None);
      u8 = (fun n -> build "MkU8" [ n ]); un_u8 = one "MkU8"; char = (fun n -> build "MkChar" [ n ]); un_char = one "MkChar";
      snil = build "SNil" []; scons = (fun ch r -> build "SCons" [ ch; r ]); un_str = (fun v -> match des "SNil" v with 1, [ ch; r ] -> Some (ch, r) | _ -> None);
      un_list = (fun v -> match des "Nil" v with 1, [ x; r ] -> Some (x, r) | _ -> None);
      un_pair = (fun v -> match des "MkPair" v with _, [ a; b ] -> (a, b) | _ -> assert false);
      un_some = (fun v -> match des "None" v with 1, [ x ] -> Some x | _ -> None);
      some = (fun x -> build "Some" [ x ]); none = build "None" []; ok = (fun x -> build "Ok" [ x ]); fail = (fun x -> build "Fail" [ x ]); unit = build "MkUnit" [];
      cons = (fun a b -> build "Cons" [ a; b ]); nil = build "Nil" []; pair = (fun a b -> build "MkPair" [ a; b ]);
      is_file = build "IsFile" []; is_dir = build "IsDir" []; is_other = build "IsOther" []; missing = build "Missing" [];
      changed = build "Changed" []; unchanged = build "Unchanged" []; mk_usage = V.VCtorFn (c "MkUsage"); mk_exited = V.VCtorFn (c "MkExited");
      request; step; is_start; apply = (fun k xs -> List.hd (Eval.apply k xs)) }

(* A message names where it is about, the file the location carries or, where it carries none, the file
   being read. A contradiction that reaches here escaped every form that would have placed it, and the
   evaluator's code has no locations at all (ASSUMPTIONS 194). *)
let explain path = function
  | Reader.Syntax (l, m) -> Some (Reader.labelled path l "syntax error: " ^ m)
  | Env.Error (l, m) -> let here = Reader.where path l in Some (Env.resolve here (Reader.label here "error: " ^ Env.framing l ^ m))
  | Env.Contradiction m -> Some (Env.resolve path (path ^ ": error: contradiction: " ^ Lazy.force m))
  | Eval.Runtime m -> Some (path ^ ": runtime error: " ^ m)
  | _ -> None

let valued = [ "--extract"; "--build"; "--confine-read"; "--confine-write"; "--comptime-unconfine"; "--confine-output-bytes"; "--hints"; "--eval-fuel"; "--goal" ]
let switches = [ "--repl"; "--no-extern"; "--no-templates"; "--no-prelude"; "--no-env"; "--no-exec"; "--no-shape-note"; "--warnings-as-errors"; "--warn-unused"; "--fn-same"; "--byte" ]

let goal_refusal mode flags =
  if mode = Elab.Unrequired then None
  else List.find_map (fun f -> if List.mem f [ "--extract"; "--build"; "--repl"; "--no-prelude" ] then Some (Printf.sprintf "--goal %s does not take %s" (Elab.goal_name mode) f) else None) flags

let compile byte src exe = exec "ocamlfind" [ (if byte then "ocamlc" else "ocamlopt"); "-package"; "zarith,unix"; "-linkpkg"; src; "-o"; exe ] (host_envs ()) None ""

let build byte path ml =
  let dir = path ^ ".build" in
  let fail code m = prerr_endline m; code in
  let guarded f = try f () with (Unix.Unix_error _ | Sys_error _) as e -> Error (Driver_core.explain e) in
  if Sys.file_exists dir then fail 3 (dir ^ ": already exists")
  else
    let src = Filename.concat dir "main.ml" in
    let ran =
      guarded (fun () ->
          Sys.mkdir dir 0o755;
          write_file src ml;
          compile byte src path)
    in
    let removed =
      guarded (fun () -> if Sys.file_exists dir then (Array.iter (fun f -> Sys.remove (Filename.concat dir f)) (Sys.readdir dir); Sys.rmdir dir); Ok ())
    in
    match ran with
    | Error m -> fail 3 m
    | Ok (code, out, err) ->
        prerr_string (out ^ err);
        if code <> 0 then fail 2 (Printf.sprintf "ocamlfind exited with code %d" code) else Result.fold ~ok:(fun () -> 0) ~error:(fail 3) removed

let goal_verdict mode passed = Printf.sprintf "--goal %s: %s" (Elab.goal_name mode) (if passed then "PASS" else "FAIL")

let consume w env ty v =
  match final env ty with
  | Main -> (driver env).run_main w v
  | Program -> let d = driver env in Eval.perform := d.perform w; w.exit (d.run_program w v)
  | Thunk t -> print w (Elab.show_value env Reader.nowhere t (List.hd (Eval.apply v [])))
  | Plain -> print w (Elab.show_value env Reader.nowhere ty v)
