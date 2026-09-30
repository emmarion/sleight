(* Runs every tests/*.sl. Directives are comment lines, read wherever in the file they sit; one that names
   a line of the test itself is written at the end, so that adding it does not move the lines it names.
   "; needs: a b" runs tests/a.sl and tests/b.sl first in the same scope;
   "; expect: text" requires that printed line; "; error: text" requires a failure mentioning text;
   "; stdin: text" lines, joined by newlines, are the input a program reads; "; args: a b" its arguments;
   "; env: NAME=value" a variable in its environment, which holds those alone;
   "; confine-dir: dir" the directory its file requests start confined to, as --confine-dir gives it;
   "; confine-output-bytes: n" the output it may write, as --confine-output-bytes gives it;
   "; no-env: yes" hides the environment from the program, as --no-env does;
   "; stderr: text" a line it must write to stderr; "; exit: n" the code an IO program must exit with;
   "; warns: text" a line the file must warn with, elaborating it or checking its indentation, whether or not it goes on to be refused;
   "; externs: only" runs the test with the FFI alone, for one whose model is too slow to run;
   "; prelude: none" runs it without lib/prelude.sl, for one that declares what it needs itself. *)
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
        if Sys.command (Printf.sprintf "ocamlfind ocamlc -custom -package zarith,unix -linkpkg %s.ml -o %s.exe > %s.log 2>&1" base base base) <> 0 then
          Some ("extracted program failed to compile, see " ^ base ^ ".log")
        else (
          write (base ^ ".in") input;
          let code =
            Sys.command
              (Printf.sprintf "env -i %s ./%s.exe %s < %s.in > %s.out 2> %s.err"
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
  Env.warn := Buffer.add_string warnings;
  let input = String.concat "\n" (directive src "stdin") in
  let lines = ref (if input = "" then [] else String.split_on_char '\n' input) in
  let read_line () = match !lines with [] -> None | l :: rest -> lines := rest; Some l in
  let read_rest () = let rest = String.concat "\n" !lines in lines := []; rest in
  let args = List.concat_map (String.split_on_char ' ') (directive src "args") in
  let envs = List.filter_map split_env (directive src "env") in
  Extract.with_env := directive src "no-env" = [];
  let visible = if !Extract.with_env then envs else [] in
  let fence = ref "/" in
  List.iter (fun d -> Result.iter_error failwith (Program.confine fence d); Extract.fence := d) (directive src "confine-dir");
  let limit = ref max_int in
  Extract.output_bytes := None;
  List.iter (fun b -> limit := Result.fold ~ok:Fun.id ~error:failwith (Program.output_limit b); Extract.output_bytes := Some b) (directive src "confine-output-bytes");
  let world =
    { Program.read_rest; read_line; out = Buffer.add_string printed; err = Buffer.add_string errors; args;
      env = (fun n -> List.assoc_opt n visible); envs = (fun () -> visible); cwd = Sys.getcwd;
      exit = (fun n -> code := n); print = (fun s -> Buffer.add_string printed (s ^ "\n")); fence; limit; used = ref 0 }
  in
  let consume = Program.consume world in
  (* The test's own final is run only after the extracted sources are taken: running it may update a unique
     Const in place, which the extracted program must start from as elaboration left it, as --extract does. *)
  let final = ref None in
  let outcome =
    try
      let one env n = let src = read (Filename.concat dir (n ^ ".sl")) in let warned = Indent.warn (label n) src in Elab.run_toplevel ~consume ~path:(label n) env (Reader.parse ~shape:(not warned) (label n) src) in
      let env = List.fold_left one (Builtin.load ~prelude:(directive src "prelude" <> [ "none" ]) ()) needs in
      Buffer.clear printed;
      Buffer.clear warnings;
      Env.trace := List.filter (function Env.Final _ -> false | _ -> true) !Env.trace;
      let warned = Indent.warn (label name) src in
      let env = Elab.run_toplevel ~consume:(fun env ty v -> final := Some (env, ty, v)) env (Reader.parse ~shape:(not warned) (label name) src) in
      let source templates = Extract.templates := templates; (try Ok (Extract.emit env (List.rev !Env.trace)) with e -> Error (Printexc.to_string e)) in
      let sources = List.map (fun t -> (t, source t)) (if externs then [ true; false ] else [ true ]) in
      Option.iter (fun (env, ty, v) -> consume env ty v) !final;
      Ok (sources, Buffer.contents printed)
    with e -> (match Program.explain (label name) e with Some m -> Error m | None -> raise e)
  in
  let at s i p = i + String.length p <= String.length s && String.sub s i (String.length p) = p in
  let rec parts pat i j =
    if j >= String.length pat then [ String.sub pat i (j - i) ]
    else if at pat j "<**>" then String.sub pat i (j - i) :: parts pat (j + 4) (j + 4)
    else parts pat i (j + 1)
  in
  let glob pat line =
    let n = String.length line in
    let rec go i = function
      | [] -> i = n
      | p :: rest -> List.exists (fun j -> at line j p && go (j + String.length p) rest) (List.init (n - i + 1) (( + ) i))
    in
    match parts pat 0 0 with first :: rest -> at line 0 first && go (String.length first) rest | [] -> false
  in
  let contains msg needle = List.exists (glob ("<**>" ^ needle ^ "<**>")) (String.split_on_char '\n' msg) in
  let lines key = String.concat "" (List.map (fun s -> s ^ "\n") (directive src key)) in
  let expect = lines "expect" and stderr = lines "stderr" in
  let exit = match directive src "exit" with [ n ] -> int_of_string n | _ -> 0 in
  let failures = directive src "error" in
  (* A warning is checked whichever way elaboration went, a refused program warning as readily as one that runs. *)
  let warned = Buffer.contents warnings in
  let mismatched_warnings =
    let got = String.split_on_char '\n' warned and want = String.split_on_char '\n' (lines "warns") in
    if List.compare_lengths got want = 0 && List.for_all2 glob want got then None else Some (Printf.sprintf "warned:\n%sexpected:\n%s" warned (lines "warns"))
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
  let names =
    match List.tl (Array.to_list Sys.argv) with
    | [] -> Sys.readdir dir |> Array.to_list |> List.filter (fun f -> Filename.check_suffix f ".sl") |> List.sort compare
    | files -> List.map (fun f -> Filename.remove_extension (Filename.basename f) ^ ".sl") files
  in
  let jobs = int_of_string (String.trim (In_channel.input_all (Unix.open_process_in "getconf _NPROCESSORS_ONLN"))) in
  let spawn f =
    let name = Filename.chop_suffix f ".sl" in
    let r, w = Unix.pipe () in
    match Unix.fork () with
    | 0 -> Unix.close r; let oc = Unix.out_channel_of_descr w in Marshal.to_channel oc (Option.map (fun m -> name ^ ": " ^ m) (try run_test name with e -> Some (Printexc.to_string e))) []; close_out oc; Unix._exit 0
    | pid -> Unix.close w; (pid, r)
  in
  let collect (pid, r) = let ic = Unix.in_channel_of_descr r in let v : string option = Marshal.from_channel ic in close_in ic; ignore (Unix.waitpid [] pid); v in
  let rec go pending running acc =
    match pending, running with
    | [], [] -> List.rev acc
    | f :: rest, _ when List.length running < jobs -> go rest (running @ [ spawn f ]) acc
    | _, _ :: _ ->
        let ready, _, _ = Unix.select (List.map snd running) [] [] (-1.) in
        let j = List.find (fun (_, r) -> r = List.hd ready) running in
        go pending (List.filter (( != ) j) running) (collect j :: acc)
    | _ :: _, [] -> assert false
  in
  let failures = List.sort compare (List.filter_map Fun.id (go names [] [])) in
  List.iter (fun m -> print_endline ("FAIL " ^ m)) failures;
  Printf.printf "%d tests, %d failures\n" (List.length names) (List.length failures);
  if failures <> [] then exit 1
