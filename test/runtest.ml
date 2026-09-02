(* Runs every tests/*.sl. Directives in leading comments:
   "; needs: a b" runs tests/a.sl and tests/b.sl first in the same scope;
   "; expect: text" requires that printed line; "; error: text" requires a failure mentioning text. *)
open Speciallang

let dir = "../tests"
let read path = let ic = open_in_bin path in let s = really_input_string ic (in_channel_length ic) in close_in ic; s

let directive src key =
  List.filter_map
    (fun line ->
      let prefix = "; " ^ key ^ ": " in
      if String.length line > String.length prefix && String.sub line 0 (String.length prefix) = prefix then
        Some (String.sub line (String.length prefix) (String.length line - String.length prefix))
      else None)
    (String.split_on_char '\n' src)

(* Every test runs with the FFI's implementations and again with them stripped (section 41's invariant). *)
let rec run_test name =
  let src = read (Filename.concat dir (name ^ ".sl")) in
  let modes = [ (true, "with externs"); (false, "without externs") ] in
  List.find_map (fun (externs, mode) -> Value.use_externs := externs; Option.map (fun m -> mode ^ ": " ^ m) (run_mode src)) modes

and run_mode src =
  let needs = List.concat_map (String.split_on_char ' ') (directive src "needs") in
  let printed = Buffer.create 64 in
  let print s = Buffer.add_string printed (s ^ "\n") in
  let outcome =
    try
      let env = List.fold_left (fun env n -> Elab.run_toplevel ~print env (Reader.parse (read (Filename.concat dir (n ^ ".sl"))))) (Builtin.load ()) needs in
      Buffer.clear printed;
      ignore (Elab.run_toplevel ~print env (Reader.parse src));
      Ok (Buffer.contents printed)
    with
    | Reader.Syntax (l, m) -> Error (Printf.sprintf "line %d: syntax error: %s" l m)
    | Env.Error (l, m) -> Error (Printf.sprintf "line %d: error: %s" l m)
    | Env.Contradiction m -> Error ("contradiction: " ^ m)
    | Eval.Runtime m -> Error ("runtime error: " ^ m)
  in
  let contains hay needle =
    let n = String.length needle and h = String.length hay in
    let rec go i = i + n <= h && (String.sub hay i n = needle || go (i + 1)) in
    go 0
  in
  let expect = String.concat "" (List.map (fun s -> s ^ "\n") (directive src "expect")) in
  let errors = directive src "error" in
  match outcome with
  | Ok out when errors = [] && out = expect -> None
  | Ok out -> Some ("ran, printed:\n" ^ out ^ (if errors = [] then "expected:\n" ^ expect else "expected an error mentioning " ^ String.concat ", " errors))
  | Error msg when List.for_all (contains msg) errors && errors <> [] -> None
  | Error msg -> Some ("failed: " ^ msg)

let () =
  let names = Sys.readdir dir |> Array.to_list |> List.filter (fun f -> Filename.check_suffix f ".sl") |> List.sort compare in
  let failures = List.filter_map (fun f -> let name = Filename.chop_suffix f ".sl" in Option.map (fun m -> name ^ ": " ^ m) (run_test name)) names in
  List.iter (fun m -> print_endline ("FAIL " ^ m)) failures;
  Printf.printf "%d tests, %d failures\n" (List.length names) (List.length failures);
  if failures <> [] then exit 1
