(* shape.ml -- report where the forms in a .sl file open and close.

   A dev tool, not part of the language. It diagnoses nothing: it states facts
   and leaves the reading to you, so it has no notion of a "correct" file and
   can never be wrong about one. It reads Reader.scan_upto's tokens, so
   comments and string literals are skipped the way the checker skips them,
   and a file the lexer cannot finish is reported as far as it got. Forms
   are identified by line:col so that two opening on the same line stay
   distinct, a position under `;! file` named and numbered as that pragma
   gives it.

   Usage:  shape [--closers] <file.sl>
             (default)  every form spanning more than one line
             --closers  what each run of ) actually closes *)

open Sleight
open Reader

let tok_text = function LParen -> "(" | RParen -> ")" | Dollar -> "$" | Item r -> Reader.show r | Invalid _ -> "?" | Pragma _ -> ";!"

type form = { at : loc; depth : int; text : string; mutable closes : loc }

let place ?(mark = "") ?(col = true) = function
  | At { file; read; line; col = c; _ } -> (if file = read then "" else file ^ ":") ^ mark ^ Z.to_string line ^ if col then ":" ^ Z.to_string c else ""
  | NoLoc | Unknown -> ""

let () =
  let closers = ref false and path = ref "" in
  Array.iteri
    (fun i a ->
      if i > 0 then
        match a with
        | "--closers" -> closers := true
        | _ -> path := a)
    Sys.argv;
  if !path = "" then (prerr_endline "usage: shape [--closers] <file.sl>"; exit 2);
  let src = match Program.read_file !path with
    | s -> s
    | exception Sys_error m -> prerr_endline m; exit 2
  in
  let toks, stopped = scan_upto !path src in
  let toks = Array.of_list toks in

  (* the first two tokens after a `(`, which is enough to recognise a form:
     "let mklets", "fun inner", "raw-cons (" *)
  let label k =
    let at j = if j < Array.length toks then (let _, _, t = toks.(j) in tok_text t) else "" in
    let a = at (k + 1) and b = at (k + 2) in
    if b = "" then a else a ^ " " ^ b
  in

  (* one pass: every ( is pushed with where it opened; every ) pops and
     records the line that closed it. A form left open keeps closes = 0. *)
  let forms = ref [] and stack = ref [] and depth = ref 0 in
  Array.iteri
    (fun k ((l : Reader.loc), _, t) ->
      match t with
      | LParen ->
          let f = { at = l; depth = !depth; text = label k; closes = nowhere } in
          forms := f :: !forms;
          stack := f :: !stack;
          incr depth
      | RParen ->
          decr depth;
          (match !stack with
           | f :: rest -> f.closes <- l; stack := rest
           | [] -> ())
      | _ -> ())
    toks;
  let forms = List.rev !forms in

  if !closers then (
    (* Group consecutive )s: what a ))))) run actually closes, in order. A
       second scan rather than a reuse of `forms`, because the first pass
       keeps each form's closing LINE -- all the default report needs -- and
       that discards exactly what a run is: which )s were ADJACENT. That
       adjacency lives only in the byte offsets, so it is read back from them. *)
    let runs = ref [] and pending = ref [] and last = ref (-1) in
    let run_line = ref nowhere and stack = ref [] in
    Array.iteri
      (fun k ((l : Reader.loc), off, t) ->
        match t with
        | LParen -> stack := (l, label k) :: !stack
        | RParen ->
            (match !stack with
             | o :: rest ->
                 if !last <> off - 1 && !pending <> [] then (
                   runs := (!run_line, List.rev !pending) :: !runs; pending := []);
                 if !pending = [] then run_line := l;
                 pending := o :: !pending;
                 last := off;
                 stack := rest
             | [] -> ())
        | _ -> ())
      toks;
    if !pending <> [] then runs := (!run_line, List.rev !pending) :: !runs;
    print_endline "closers";
    List.iter
      (fun (ln, os) ->
        if List.length os > 1 then
          Printf.printf "  %-5s %2d closers -> %s\n" (place ~mark:"L" ~col:false ln) (List.length os)
            (String.concat "  " (List.map (fun (l, t) -> Printf.sprintf "%s@%s" t (place l)) os)))
      (List.rev !runs))
  else (
    print_endline "depth  opens     form                      closes";
    List.iter
      (fun f ->
        if f.closes = nowhere || fst (coords f.closes) <> fst (coords f.at) then
          Printf.printf "%5d  %-9s %-25s %s\n" f.depth (place f.at) f.text
            (if f.closes = nowhere then "NEVER" else place ~mark:"L" ~col:false f.closes))
      forms);

  Printf.printf "final depth %d%s\n" !depth
    (if !depth > 0 then "  (unclosed forms: append that many )"
     else if !depth < 0 then "  (surplus ))"
     else "");

  match stopped with
  | None -> ()
  | Some (l, m) ->
      Printf.eprintf "%s: %s -- everything above is what was read before that\n" (Reader.where !path l) m;
      exit 2
