(* Runs every tests/*.sl. Directives in leading comments:
   "; needs: a b" runs tests/a.sl and tests/b.sl first in the same scope;
   "; expect: text" requires that printed line; "; error: text" requires a failure mentioning text;
   "; stdin: text" lines, joined by newlines, are the input a program reads; "; args: a b" its arguments;
   "; stderr: text" a line it must write to stderr; "; exit: n" the code an IO program must exit with. *)
open Speciallang

let dir = "../tests"
let read = Program.read_file and write = Program.write_file

let directive src key =
  let prefix = "; " ^ key ^ ": " in
  let value line = if String.starts_with ~prefix line then Some (String.sub line (String.length prefix) (String.length line - String.length prefix)) else None in
  List.filter_map value (String.split_on_char '\n' src)

let ocamlfind = lazy (Sys.command "ocamlfind ocamlopt -version > /dev/null 2>&1" = 0)

let report out err code expect stderr exit =
  Printf.sprintf "printed:\n%sstderr:\n%sexit %d\nexpected:\n%sstderr:\n%sexit %d" out err code expect stderr exit

let extracted name externs templates env input args expect stderr exit =
  if not (Lazy.force ocamlfind) then Some "ocamlfind is not available to compile the extracted program"
  else
    let base = Filename.concat "extract" (name ^ if not externs then "_src" else if templates then "_ffi" else "_ffi_view") in
    Extract.templates := templates;
    (try Sys.mkdir "extract" 0o755 with Sys_error _ -> ());
    let outcome =
      try
        write (base ^ ".ml") (Extract.emit env (List.rev !Env.trace));
        Ok ()
      with e -> Error (Printexc.to_string e)
    in
    match outcome with
    | Error m -> Some ("extraction failed: " ^ m)
    | Ok () ->
        if Sys.command (Printf.sprintf "ocamlfind ocamlopt -package zarith -linkpkg %s.ml -o %s.exe > %s.log 2>&1" base base base) <> 0 then
          Some ("extracted program failed to compile, see " ^ base ^ ".log")
        else (
          write (base ^ ".in") input;
          let code =
            Sys.command
              (Printf.sprintf "./%s.exe -- %s < %s.in > %s.out 2> %s.err" base (String.concat " " (List.map Filename.quote args)) base base base)
          in
          let out = read (base ^ ".out") and err = read (base ^ ".err") in
          if out = expect && err = stderr && code = exit then None else Some ("extracted program " ^ report out err code expect stderr exit))

(* Every test runs with the FFI's implementations and again with them stripped (section 41's invariant). *)
let rec run_test name =
  let src = read (Filename.concat dir (name ^ ".sl")) in
  let modes = [ (true, "with externs"); (false, "without externs") ] in
  List.find_map (fun (externs, mode) -> Value.use_externs := externs; Option.map (fun m -> mode ^ ": " ^ m) (run_mode name externs src)) modes

and run_mode name externs src =
  let needs = List.concat_map (String.split_on_char ' ') (directive src "needs") in
  let printed = Buffer.create 64 and errors = Buffer.create 64 and code = ref 0 in
  let input = String.concat "\n" (directive src "stdin") in
  let lines = ref (if input = "" then [] else String.split_on_char '\n' input) in
  let read_line () = match !lines with [] -> None | l :: rest -> lines := rest; Some l in
  let args = List.concat_map (String.split_on_char ' ') (directive src "args") in
  let world =
    { Program.input = (fun () -> input); read_line; out = Buffer.add_string printed; err = Buffer.add_string errors; args;
      exit = (fun n -> code := n); print = (fun s -> Buffer.add_string printed (s ^ "\n")) }
  in
  let consume = Program.consume world in
  let outcome =
    try
      let env = List.fold_left (fun env n -> Elab.run_toplevel ~consume env (Reader.parse (read (Filename.concat dir (n ^ ".sl"))))) (Builtin.load ()) needs in
      Buffer.clear printed;
      Env.trace := List.filter (function Env.Final _ -> false | _ -> true) !Env.trace;
      let env = Elab.run_toplevel ~consume env (Reader.parse src) in
      Ok (env, Buffer.contents printed)
    with e -> (match Program.explain name e with Some m -> Error m | None -> raise e)
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
  match outcome with
  | Ok (env, out) when failures = [] && out = expect && Buffer.contents errors = stderr && !code = exit ->
      (* With the FFI the program is extracted twice, through the extern templates and through the views alone. *)
      (match extracted name externs true env input args expect stderr exit with
       | None when externs -> Option.map (fun m -> "without templates: " ^ m) (extracted name externs false env input args expect stderr exit)
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
