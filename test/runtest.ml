(* Runs every tests/*.sl. Directives in leading comments:
   "; needs: a b" runs tests/a.sl and tests/b.sl first in the same scope;
   "; expect: text" requires that printed line; "; error: text" requires a failure mentioning text;
   "; stdin: text" lines, joined by newlines, are the input a program reads; "; args: a b" its arguments;
   "; env: NAME=value" a variable in its environment, which holds those alone;
   "; stderr: text" a line it must write to stderr; "; exit: n" the code an IO program must exit with;
   "; warns: text" a line the file must warn with, elaborating it or checking its indentation, whether or not it goes on to be refused;
   "; externs: only" runs the test with the FFI alone, for one whose model is too slow to run. *)
open Speciallang

let dir = "../tests"
let read = Program.read_file and write = Program.write_file

(* The path from the repository root, which is what bootstrap.sh hands slc, not the path read from here. *)
let label name = "tests/" ^ name ^ ".sl"

let directive src key =
  let prefix = "; " ^ key ^ ": " in
  let value line = if String.starts_with ~prefix line then Some (String.sub line (String.length prefix) (String.length line - String.length prefix)) else None in
  List.filter_map value (String.split_on_char '\n' src)

let ocamlfind = lazy (Sys.command "ocamlfind ocamlopt -version > /dev/null 2>&1" = 0)

let report out err code expect stderr exit =
  Printf.sprintf "printed:\n%sstderr:\n%sexit %d\nexpected:\n%sstderr:\n%sexit %d" out err code expect stderr exit

let split_env s = Option.map (fun i -> (String.sub s 0 i, String.sub s (i + 1) (String.length s - i - 1))) (String.index_opt s '=')

let extracted name externs templates source input args envs expect stderr exit =
  if not (Lazy.force ocamlfind) then Some "ocamlfind is not available to compile the extracted program"
  else
    let base = Filename.concat "extract" (name ^ if not externs then "_src" else if templates then "_ffi" else "_ffi_view") in
    (try Sys.mkdir "extract" 0o755 with Sys_error _ -> ());
    match source with
    | Error m -> Some ("extraction failed: " ^ m)
    | Ok text ->
        write (base ^ ".ml") text;
        if Sys.command (Printf.sprintf "ocamlfind ocamlopt -package zarith,unix -linkpkg %s.ml -o %s.exe > %s.log 2>&1" base base base) <> 0 then
          Some ("extracted program failed to compile, see " ^ base ^ ".log")
        else (
          write (base ^ ".in") input;
          let code =
            Sys.command
              (Printf.sprintf "env -i %s ./%s.exe -- %s < %s.in > %s.out 2> %s.err"
                 (String.concat " " (List.map (fun (n, v) -> Filename.quote (n ^ "=" ^ v)) envs))
                 base (String.concat " " (List.map Filename.quote args)) base base base)
          in
          let out = read (base ^ ".out") and err = read (base ^ ".err") in
          if out = expect && err = stderr && code = exit then None else Some ("extracted program " ^ report out err code expect stderr exit))

(* Every test runs with the FFI's implementations and again with them stripped (section 41's invariant). *)
let rec run_test name =
  let src = read (Filename.concat dir (name ^ ".sl")) in
  let modes = [ (true, "with externs"); (false, "without externs") ] in
  let modes = if directive src "externs" = [ "only" ] then [ List.hd modes ] else modes in
  List.find_map (fun (externs, mode) -> Value.use_externs := externs; Option.map (fun m -> mode ^ ": " ^ m) (run_mode name externs src)) modes

and run_mode name externs src =
  let needs = List.concat_map (String.split_on_char ' ') (directive src "needs") in
  let printed = Buffer.create 64 and errors = Buffer.create 64 and warnings = Buffer.create 64 and code = ref 0 in
  Elab.warn := Buffer.add_string warnings;
  let input = String.concat "\n" (directive src "stdin") in
  let lines = ref (if input = "" then [] else String.split_on_char '\n' input) in
  let read_line () = match !lines with [] -> None | l :: rest -> lines := rest; Some l in
  let read_rest () = let rest = String.concat "\n" !lines in lines := []; rest in
  let args = List.concat_map (String.split_on_char ' ') (directive src "args") in
  let envs = List.filter_map split_env (directive src "env") in
  let world =
    { Program.read_rest; read_line; out = Buffer.add_string printed; err = Buffer.add_string errors; args;
      env = (fun n -> List.assoc_opt n envs); envs = (fun () -> envs); cwd = Sys.getcwd;
      exit = (fun n -> code := n); print = (fun s -> Buffer.add_string printed (s ^ "\n")) }
  in
  let consume = Program.consume world in
  (* The test's own final is run only after the extracted sources are taken: running it may update a unique
     Const in place, which the extracted program must start from as elaboration left it, as --extract does. *)
  let final = ref None in
  let outcome =
    try
      let one env n = let src = read (Filename.concat dir (n ^ ".sl")) in Indent.warn (label n) src; Elab.run_toplevel ~consume ~path:(label n) env (Reader.parse (label n) src) in
      let env = List.fold_left one (Builtin.load ()) needs in
      Buffer.clear printed;
      Buffer.clear warnings;
      Env.trace := List.filter (function Env.Final _ -> false | _ -> true) !Env.trace;
      Indent.warn (label name) src;
      let env = Elab.run_toplevel ~consume:(fun env ty v -> final := Some (env, ty, v)) env (Reader.parse (label name) src) in
      let source templates = Extract.templates := templates; (try Ok (Extract.emit env (List.rev !Env.trace)) with e -> Error (Printexc.to_string e)) in
      let sources = List.map (fun t -> (t, source t)) (if externs then [ true; false ] else [ true ]) in
      Option.iter (fun (env, ty, v) -> consume env ty v) !final;
      Ok (sources, Buffer.contents printed)
    with e -> (match Program.explain (label name) e with Some m -> Error m | None -> raise e)
  in
  let contains hay needle =
    let n = String.length needle and h = String.length hay in
    let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
    go 0
  in
  let lines key = String.concat "" (List.map (fun s -> s ^ "\n") (directive src key)) in
  let expect = lines "expect" and stderr = lines "stderr" in
  let exit = match directive src "exit" with [ n ] -> int_of_string n | _ -> 0 in
  let failures = directive src "error" in
  (* A warning is checked whichever way elaboration went, a refused program warning as readily as one that runs. *)
  let warned = Buffer.contents warnings in
  let mismatched_warnings =
    if warned = lines "warns" then None else Some (Printf.sprintf "warned:\n%sexpected:\n%s" warned (lines "warns"))
  in
  match outcome with
  | _ when mismatched_warnings <> None -> mismatched_warnings
  | Ok (sources, out) when failures = [] && out = expect && Buffer.contents errors = stderr && !code = exit ->
      (* With the FFI the program is extracted twice, through the extern templates and through the views alone. *)
      (match extracted name externs true (List.assoc true sources) input args envs expect stderr exit with
       | None when externs -> Option.map (fun m -> "without templates: " ^ m) (extracted name externs false (List.assoc false sources) input args envs expect stderr exit)
       | r -> r)
  | Ok (_, out) ->
      Some
        (Printf.sprintf "ran, %s"
           (if failures = [] then report out (Buffer.contents errors) !code expect stderr exit
            else "expected an error mentioning " ^ String.concat ", " failures))
  | Error msg when List.for_all (contains msg) failures && failures <> [] -> None
  | Error msg -> Some ("failed: " ^ msg)

let () =
  let names = Sys.readdir dir |> Array.to_list |> List.filter (fun f -> Filename.check_suffix f ".sl") |> List.sort compare in
  let failures = List.filter_map (fun f -> let name = Filename.chop_suffix f ".sl" in Option.map (fun m -> name ^ ": " ^ m) (run_test name)) names in
  List.iter (fun m -> print_endline ("FAIL " ^ m)) failures;
  Printf.printf "%d tests, %d failures\n" (List.length names) (List.length failures);
  if failures <> [] then exit 1
