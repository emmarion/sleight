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

(* Arguments after "--" belong to the program (its GetArgs request); the rest are files and flags. *)
let () =
  let rec split acc = function [] -> (List.rev acc, []) | "--" :: rest -> (List.rev acc, rest) | a :: rest -> split (a :: acc) rest in
  let args, program_args = split [] (List.tl (Array.to_list Sys.argv)) in
  let rec option name acc = function f :: v :: rest when f = name -> (Some v, List.rev_append acc rest) | a :: rest -> option name (a :: acc) rest | [] -> (None, List.rev acc) in
  let extract, args = option "--extract" [] args in
  let confine, args = option "--confine-dir" [] args in
  Option.iter (( := ) Extract.fence) confine;
  let output_bytes, args = option "--confine-output-bytes" [] args in
  Extract.output_bytes := output_bytes;
  let hints, args = option "--hints" [] args in
  Option.iter (fun p -> Special.help := Program.read_file p) hints;
  let flag f = List.mem f args in
  Value.use_externs := not (flag "--no-extern");
  Extract.templates := not (flag "--no-templates");
  Extract.with_env := not (flag "--no-env");
  Reader.shape_notes := not (flag "--no-shape-note");
  let consume = if extract = None then Program.consume (Program.start !Extract.fence !Extract.output_bytes !Extract.with_env (world program_args)) else fun _ _ _ -> () in
  let env = Builtin.load ~prelude:(not (flag "--no-prelude")) () in
  let env =
    match List.filter (fun a -> not (List.mem a [ "--repl"; "--no-extern"; "--no-templates"; "--no-prelude"; "--no-env"; "--no-shape-note" ])) args with
    | [] when not (flag "--repl") -> run consume env "-"
    | files ->
        let env = List.fold_left (run consume) env files in
        if flag "--repl" then repl consume env;
        env
  in
  Option.iter (fun path -> Out_channel.with_open_bin path (fun oc -> output_string oc (Extract.emit env (List.rev !Env.trace)))) extract
