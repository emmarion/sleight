open Speciallang

let read_file path =
  let ic = open_in_bin path in
  let s = really_input_string ic (in_channel_length ic) in
  close_in ic;
  s

let report path f =
  try f () with
  | Reader.Syntax (line, msg) -> Printf.eprintf "%s:%d: syntax error: %s\n%!" path line msg; None
  | Env.Error (line, msg) -> Printf.eprintf "%s:%d: error: %s\n%!" path line msg; None
  | Env.Contradiction msg -> Printf.eprintf "%s: error: contradiction: %s\n%!" path msg; None
  | Eval.Runtime msg -> Printf.eprintf "%s: runtime error: %s\n%!" path msg; None

let run env path =
  let src = if path = "-" then In_channel.input_all stdin else read_file path in
  match report path (fun () -> Some (Elab.run_toplevel env (Reader.parse src))) with Some env -> env | None -> exit 1

(* Reads forms until each is complete, running statements and printing expressions; an error keeps the scope as it was. *)
let repl env =
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
    | Some src -> loop (Option.value (report "repl" (fun () -> Some (Elab.run_toplevel env (Reader.parse src)))) ~default:env)
  in
  loop env

let () =
  match List.tl (Array.to_list Sys.argv) with
  | [] -> ignore (run Prelude.env "-")
  | args ->
      let files, interactive = List.partition (( <> ) "--repl") args in
      let env = List.fold_left run Prelude.env files in
      if interactive <> [] then repl env
