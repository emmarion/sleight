open Speciallang

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let () =
  let files = List.tl (Array.to_list Sys.argv) in
  if files = [] then (prerr_endline "usage: main FILE..."; exit 2);
  let run env path =
    try Elab.run_toplevel env (Reader.parse (read_file path)) with
    | Reader.Syntax (line, msg) -> Printf.eprintf "%s:%d: syntax error: %s\n" path line msg; exit 1
    | Env.Error (line, msg) -> Printf.eprintf "%s:%d: error: %s\n" path line msg; exit 1
    | Env.Contradiction msg -> Printf.eprintf "%s: error: contradiction: %s\n" path msg; exit 1
    | Elab.BranchAbsurd _ -> Printf.eprintf "%s: error: comptime-match contradicts the facts in force\n" path; exit 1
    | Eval.Runtime msg -> Printf.eprintf "%s: runtime error: %s\n" path msg; exit 1
  in
  ignore (List.fold_left run Prelude.env files)
