open Speciallang

let report path f = try Some (f ()) with e -> (match Program.explain path e with Some m -> prerr_endline m; None | None -> raise e)

let world args =
  let flush_to oc s = output_string oc s; flush oc in
  { Program.read_rest = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin);
    out = flush_to stdout; err = flush_to stderr; args; env = Sys.getenv_opt; envs = Program.host_envs; cwd = Sys.getcwd;
    exit; print = print_endline; fence = ref "/"; limit = ref max_int; used = ref 0 }

let run consume env path =
  let src = if path = "-" then In_channel.input_all stdin else Program.read_file path in
  let warned = Speciallang.Indent.warn path src in
  match report path (fun () -> Elab.run_toplevel ~consume ~path env (Reader.parse ~shape:(not warned) path src)) with Some env -> env | None -> exit 1

(* Reads forms until each is complete, running statements and printing expressions; an error keeps the scope as it was. *)
let repl consume env =
  let balance s = String.fold_left (fun n c -> match c with '(' -> n + 1 | ')' -> n - 1 | _ -> n) 0 s in
  let rec form buf =
    print_string (if Buffer.length buf = 0 then "> " else "  ");
    match In_channel.input_line stdin with
    | None -> None
    | Some line ->
        Buffer.add_string buf (line ^ "\n");
        if balance (Buffer.contents buf) > 0 then form buf else Some (Buffer.contents buf)
  in
  let rec loop env =
    match form (Buffer.create 64) with
    | None -> print_newline ()
    | Some src -> loop (Option.value (report "repl" (fun () -> Elab.run_toplevel ~consume ~path:"repl" env (Reader.parse "repl" src))) ~default:env)
  in
  loop env

(* Arguments after "--" belong to the program (its GetArgs request); the rest are files and flags, in any order, the
   flags in [valued] each taking the argument after it; a flag given twice takes its last value. *)
let () =
  let rec split acc = function [] -> (List.rev acc, []) | "--" :: rest -> (List.rev acc, rest) | a :: rest -> split (a :: acc) rest in
  let args, program_args = split [] (List.tl (Array.to_list Sys.argv)) in
  let valued = [ "--extract"; "--confine-dir"; "--confine-output-bytes"; "--hints" ]
  and switches = [ "--repl"; "--no-extern"; "--no-templates"; "--no-prelude"; "--no-env"; "--no-shape-note"; "--warnings-as-errors" ] in
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
  let extract = option "--extract" in
  Option.iter (( := ) Extract.fence) (option "--confine-dir");
  Extract.output_bytes := option "--confine-output-bytes";
  Option.iter (fun p -> Special.help := Program.read_file p) (option "--hints");
  Value.use_externs := not (flag "--no-extern");
  Extract.templates := not (flag "--no-templates");
  Extract.with_env := not (flag "--no-env");
  Reader.shape_notes := not (flag "--no-shape-note");
  let consume = if extract = None then Program.consume (Program.start !Extract.fence !Extract.output_bytes !Extract.with_env (world program_args)) else fun _ _ _ -> () in
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
  let env = Builtin.load ~prelude:(not (flag "--no-prelude")) () in
  let env =
    match files with
    | [] when not (flag "--repl") -> settle (run held env "-")
    | files ->
        let env = settle (List.fold_left (run held) env files) in
        if flag "--repl" then repl consume env;
        settle env
  in
  Option.iter (fun path -> Out_channel.with_open_bin path (fun oc -> output_string oc (Extract.emit env (List.rev !Env.trace)))) extract
