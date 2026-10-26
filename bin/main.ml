open Sleight

let report path f = try Some (f ()) with e -> (match Program.explain path e with Some m -> prerr_endline m; None | None -> raise e)

let world args =
  let flush_to oc s = output_string oc s; flush oc in
  { Program.read_rest = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin);
    out = flush_to stdout; err = flush_to stderr; args; env = Sys.getenv_opt; envs = Program.host_envs; cwd = Sys.getcwd;
    exit; print = print_endline; exec = true; fence = ref Program.unconfined; limit = ref None; used = ref 0 }

let run consume (env, _) path =
  let src = if path = "-" then In_channel.input_all stdin else Program.read_file path in
  let files = Reader.files path src in
  List.fold_left
    (fun (env, _) (f : Reader.file) -> match report f.name (fun () -> Elab.run_file ~consume env f) with Some env -> (env, f.name) | None -> exit 1)
    (env, path) files

(* Reads forms until each is complete, running statements and printing expressions; an error keeps the scope, the goal and the
   trace as they were, but for the unique entries code that ran before it consumed. *)
let repl consume env =
  let consumed = ref Env.IntMap.empty in
  let keep = Env.IntMap.union (fun _ u _ -> Some u) in
  Elab.on_run := (fun e -> consumed := keep (Env.IntMap.filter (fun _ (u, _) -> u = Env.Consumed) e.Env.uses) !consumed);
  let unfinished src =
    match List.rev (Reader.files "repl" src) with
    | { stopped = Some (_, m); _ } :: _ -> m = Reader.unterminated
    | f :: _ -> (match Sleight.Indent.balance f.toks with _ :: _, None -> true | _ -> false)
    | [] -> false
  in
  let rec form buf =
    print_string (if Buffer.length buf = 0 then "> " else "  ");
    match In_channel.input_line stdin with
    | None -> if Buffer.length buf = 0 then None else Some (Buffer.contents buf)
    | Some line ->
        Buffer.add_string buf (line ^ "\n");
        if unfinished (Buffer.contents buf) then form buf else Some (Buffer.contents buf)
  in
  let rec loop env =
    match form (Buffer.create 64) with
    | None -> print_newline ()
    | Some src ->
        consumed := Env.IntMap.empty;
        let trace = !Env.trace and goal = !Elab.goal and discharged = !Elab.discharged in
        loop
          (match report "repl" (fun () -> List.fold_left (fun env f -> Elab.run_toplevel ~consume ~path:"repl" env (Reader.parse f)) env (Reader.files "repl" src)) with
           | Some env -> env
           | None ->
               Env.trace := trace;
               Elab.goal := goal;
               Elab.discharged := discharged;
               { env with Env.uses = keep (Env.IntMap.filter (fun x _ -> Env.IntMap.mem x env.Env.entries) !consumed) env.uses })
  in
  loop env

(* Arguments after "--" belong to the program (its GetArgs request); the rest are files and flags, in any order, the
   flags in [valued] each taking the argument after it; a flag given twice takes its last value, but for
   --comptime-unconfine, --confine-read and --confine-write, which take each. *)
let () =
  let rec split acc = function [] -> (List.rev acc, []) | "--" :: rest -> (List.rev acc, rest) | a :: rest -> split (a :: acc) rest in
  let args, program_args = split [] (List.tl (Array.to_list Sys.argv)) in
  let valued = Program.valued and switches = Program.switches in
  let rec read flags files = function
    | [] -> (flags, List.rev files)
    | f :: v :: rest when List.mem f valued -> read ((f, v) :: flags) files rest
    | f :: rest when List.mem f switches -> read ((f, "") :: flags) files rest
    | f :: _ when String.starts_with ~prefix:"--" f ->
        prerr_endline (if List.mem f valued then f ^ " needs a value" else "unknown flag " ^ f);
        exit 1
    | file :: rest -> read flags (file :: files) rest
  in
  let flags, files = read [] [] args in
  let option f = List.assoc_opt f flags and flag f = List.mem_assoc f flags in
  let extract = option "--extract" and build = option "--build" in
  let values f = List.rev (List.filter_map (fun (g, v) -> if g = f then Some v else None) flags) in
  Extract.reads := values "--confine-read";
  Extract.writes := values "--confine-write";
  Extract.output_bytes := option "--confine-output-bytes";
  Option.iter (fun p -> Special.help := Program.read_file p) (option "--hints");
  Option.iter (fun f -> match Ffi_core.nat_of_string f with Some n when Z.fits_int n -> Eval.fuel := Some (Z.to_int n) | _ -> prerr_endline "--eval-fuel takes a number of steps"; exit 1) (option "--eval-fuel");
  Value.use_externs := not (flag "--no-extern");
  Extract.templates := not (flag "--no-templates");
  Extract.with_env := not (flag "--no-env");
  Extract.with_exec := not (flag "--no-exec");
  Reader.shape_notes := not (flag "--no-shape-note");
  let fail m = prerr_endline m; exit 1 in
  if flag "--byte" && build = None then fail "--byte needs --build";
  Elab.goal_mode := Option.fold ~none:Elab.Unrequired ~some:(fun m -> match List.assoc_opt m Elab.goal_modes with Some m -> m | None -> fail "--goal takes none, open or proved") (option "--goal");
  let passed = ref false in
  if !Elab.goal_mode <> Elab.Unrequired then at_exit (fun () -> print_endline (Program.goal_verdict !Elab.goal_mode !passed));
  Option.iter fail (Program.goal_refusal !Elab.goal_mode (List.map fst flags));
  let consume = if extract = None && build = None then Program.consume (Program.start !Extract.reads !Extract.writes !Extract.output_bytes !Extract.with_env !Extract.with_exec (world program_args)) else fun _ _ _ -> () in
  let warned = ref false and pending = ref [] in
  let strict = flag "--warnings-as-errors" in
  if strict then (let warn = !Env.warn in Env.warn := fun s -> warned := true; warn s);
  let held = if strict then fun env ty v -> pending := (fun () -> consume env ty v) :: !pending else consume in
  let settle env =
    if !warned then (prerr_endline "warnings are treated as errors (--warnings-as-errors)"; exit 1);
    List.iter (fun f -> f ()) (List.rev !pending);
    pending := [];
    env
  in
  Env.warn_unused := flag "--warn-unused";
  Env.fn_same := flag "--fn-same";
  let env = match report "lib/prelude.sl" (Builtin.load ~prelude:(not (flag "--no-prelude"))) with Some env -> env | None -> exit 1 in
  Elab.sources := List.filter_map (fun f -> if f = "-" then None else Some (f, Elab.source_dir f)) files @ List.map (fun v -> (v, Elab.source_dir v)) (values "--comptime-unconfine");
  let files = if files = [] && not (flag "--repl") then [ "-" ] else files in
  let env, final = List.fold_left (run held) (env, "-") files in
  let env = settle env in
  if flag "--repl" then repl consume env;
  let env = settle env in
  if !Elab.goal_mode <> Elab.Unrequired then
    match report final Elab.close_goal with Some report -> Option.iter prerr_endline report; passed := true | None -> exit 1
  else
  let ml = lazy (Extract.emit env (List.rev !Env.trace)) in
  Option.iter (fun path -> Out_channel.with_open_bin path (fun oc -> output_string oc (Lazy.force ml))) extract;
  Option.iter (fun path -> let code = Program.build (flag "--byte") path (Lazy.force ml) in if code <> 0 then exit code) build
