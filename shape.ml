(* shape.ml -- report where the forms in a .sp file open and close.

   A dev tool, not part of the language. It diagnoses nothing: it states facts
   and leaves the reading to you, so it has no notion of a "correct" file and
   can never be wrong about one.

   `tests/README.md` is the documentation -- how to read the output, why the
   two kinds of paren mistake look different, and what this deliberately does
   not do. Forms are identified by line:col so that two opening on the same
   line stay distinct.

   Usage:  shape [--closers] <file.sp>
             (default)  every form spanning more than one line
             --closers  what each run of ) actually closes *)

let read_file path =
  let ic = open_in_bin path in
  let n = in_channel_length ic in
  let s = really_input_string ic n in
  close_in ic; s

(* the first two tokens after a `(`, which is enough to recognise a form:
   "let mklets", "fun inner", "raw-cons (" *)
let label src i =
  let n = String.length src in
  let is_sep c = c = ' ' || c = '\n' || c = '\t' in
  let rec skip j = if j < n && is_sep src.[j] then skip (j + 1) else j in
  let tok j =
    let j = skip j in
    if j >= n then ("", j)
    else if src.[j] = '(' || src.[j] = ')' then (String.make 1 src.[j], j + 1)
    else
      let k = ref j in
      while !k < n && not (is_sep src.[!k]) && src.[!k] <> '(' && src.[!k] <> ')' do
        incr k
      done;
      (String.sub src j (!k - j), !k)
  in
  let a, j = tok (i + 1) in
  let b, _ = tok j in
  if b = "" then a else a ^ " " ^ b

type form = { line : int; col : int; depth : int; text : string; mutable closes : int }

let () =
  let closers = ref false and path = ref "" in
  Array.iteri
    (fun i a ->
      if i > 0 then
        match a with
        | "--closers" -> closers := true
        | _ -> path := a)
    Sys.argv;
  if !path = "" then (prerr_endline "usage: shape [--closers] <file.sp>"; exit 2);
  let src = match read_file !path with
    | s -> s
    | exception Sys_error m -> prerr_endline m; exit 2
  in

  (* one pass: every ( is pushed with where it opened; every ) pops and
     records the line that closed it. A form left open keeps closes = 0. *)
  let forms = ref [] and stack = ref [] in
  let line = ref 1 and col = ref 1 and depth = ref 0 in
  String.iteri
    (fun i c ->
      (match c with
       | '(' ->
           let f = { line = !line; col = !col; depth = !depth;
                     text = label src i; closes = 0 } in
           forms := f :: !forms;
           stack := f :: !stack;
           incr depth
       | ')' ->
           decr depth;
           (match !stack with
            | f :: rest -> f.closes <- !line; stack := rest
            | [] -> ())
       | _ -> ());
      if c = '\n' then (incr line; col := 1) else incr col)
    src;
  let forms = List.rev !forms in

  if !closers then (
    (* Group consecutive )s: what a ))))) run actually closes, in order. A
       second scan rather than a reuse of `forms`, because the first pass
       keeps each form's closing LINE -- all the default report needs -- and
       that discards exactly what a run is: which )s were ADJACENT. That
       adjacency lives only in the text, so it is read back from the text. *)
    let runs = ref [] and pending = ref [] and last = ref (-1) in
    let line = ref 1 and col = ref 1 and run_line = ref 1 in
    let stack = ref [] in
    String.iteri
      (fun i c ->
        (match c with
         | '(' -> stack := ((!line, !col), label src i) :: !stack
         | ')' ->
             (match !stack with
              | o :: rest ->
                  if !last <> i - 1 && !pending <> [] then (
                    runs := (!run_line, List.rev !pending) :: !runs; pending := []);
                  if !pending = [] then run_line := !line;
                  pending := o :: !pending;
                  last := i;
                  stack := rest
              | [] -> ())
         | _ -> ());
        if c = '\n' then (incr line; col := 1) else incr col)
      src;
    if !pending <> [] then runs := (!run_line, List.rev !pending) :: !runs;
    print_endline "closers";
    List.iter
      (fun (ln, os) ->
        if List.length os > 1 then
          Printf.printf "  L%-4d %2d closers -> %s\n" ln (List.length os)
            (String.concat "  "
               (List.map (fun ((l, c), t) -> Printf.sprintf "%s@%d:%d" t l c) os)))
      (List.rev !runs))
  else (
    print_endline "depth  opens     form                      closes";
    List.iter
      (fun f ->
        if f.closes <> f.line || f.closes = 0 then
          Printf.printf "%5d  %-9s %-25s %s\n" f.depth
            (Printf.sprintf "%d:%d" f.line f.col) f.text
            (if f.closes = 0 then "NEVER" else Printf.sprintf "L%d" f.closes))
      forms);

  Printf.printf "final depth %d%s\n" !depth
    (if !depth > 0 then "  (unclosed forms: append that many )"
     else if !depth < 0 then "  (surplus ))"
     else "")
