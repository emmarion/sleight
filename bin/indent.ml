(* indent.ml -- checks that a .sl file's indentation tracks its paren nesting.

   A dev tool, not part of the language, in the spirit of shape.ml: it reads
   Reader.scan_upto's tokens rather than re-scanning bytes, so it skips
   comments and strings exactly the way the real reader does, and reports the
   same partial result shape.ml would if the file doesn't fully lex.

   Rule, one line: indentation is read as a claim about paren nesting, and
   this checks the claim. Spelled out --

     - indentation must be spaces only, no tabs;
     - only relative indentation and relative nesting matter, never their
       absolute values;
     - two lines at the same indentation must start at the same nesting;
     - a more indented line must start more nested than the one before it;
     - a less indented line is checked against every indentation level still
       "open" above it: each must have been more nested, and if the new
       line's indentation exactly matches one still open, its nesting must
       match too.

   $ is not paren nesting and is deliberately not tracked: a $ chain closes
   only at its enclosing form's terminator, so counting it would make the
   common flat-aligned $ chain (self/header.sl, self/core.sl's sp-table)
   look like it plunges one level deeper on every line, which is worse than
   ignoring it. Blank lines and comment-only lines carry no tokens and are
   silently skipped, matching the reader. *)

open Speciallang
open Reader

let issues = ref 0

let report path line msg =
  incr issues;
  Printf.printf "%s:%d: %s\n" path line msg

let col_of src off =
  let rec bol i = if i <= 0 then 0 else if src.[i - 1] = '\n' then i else bol (i - 1) in
  off - bol off + 1

type checkable = { line : int; indent : int; nesting : int }

(* One line is "checkable" when a token starts on it; its indent is that
   token's column, and its nesting is the paren depth in effect just before
   that token -- i.e. before the line's own characters are read. *)
let checkable_lines path src toks =
  let depth = ref 0 and cur_line = ref 0 and out = ref [] in
  List.iter
    (fun (line, off, tok) ->
       if line <> !cur_line then begin
         cur_line := line;
         let col = col_of src off in
         let bol = off - (col - 1) in
         if String.exists (( = ) '\t') (String.sub src bol (off - bol)) then
           report path line "indentation uses a tab, not spaces only";
         out := { line; indent = col - 1; nesting = !depth } :: !out
       end;
       match tok with
       | LParen -> incr depth
       | RParen -> decr depth
       | Dollar | Word _ -> ())
    toks;
  List.rev !out

(* The indentation/nesting stack: (indent, nesting) list, head = innermost. *)
let check_lines path lines =
  let stack = ref [] in
  List.iter
    (fun { line = l; indent = i; nesting = n } ->
       match !stack with
       | [] -> stack := [ (i, n) ]
       | (top_i, top_n) :: _ when i = top_i ->
           if n <> top_n then
             report path l
               (Printf.sprintf
                  "same indentation (%d) as the previous checked line but nesting is %d, expected %d (matching that line)"
                  i n top_n);
           stack := (i, n) :: List.tl !stack
       | (top_i, top_n) :: _ when i > top_i ->
           if n <= top_n then
             report path l
               (Printf.sprintf "indentation increased (%d -> %d) but nesting did not increase (%d -> %d)" top_i i top_n n);
           stack := (i, n) :: !stack
       | _ ->
           let rec pop s =
             match s with
             | (ei, en) :: rest when ei > i ->
                 if not (en > n) then
                   report path l
                     (Printf.sprintf
                        "dedented past indentation %d (nesting %d), but this line's nesting is %d (expected less than %d)"
                        ei en n en);
                 pop rest
             | _ -> s
           in
           let remaining = pop !stack in
           List.iter
             (fun (ei, en) ->
                if ei < i && not (en < n) then
                  report path l
                    (Printf.sprintf
                       "dedented to indentation %d, but an enclosing line at indentation %d has nesting %d, not less than this line's %d"
                       i ei en n))
             remaining;
           (match remaining with
            | (ei, en) :: rest when ei = i ->
                if en <> n then
                  report path l
                    (Printf.sprintf
                       "dedented back to indentation %d, matching an earlier line, but nesting is %d there vs %d here" i en n);
                stack := (i, n) :: rest
            | _ -> stack := (i, n) :: remaining))
    lines

let check_file path =
  let src = match Program.read_file path with s -> s | exception Sys_error m -> prerr_endline m; exit 2 in
  let toks, stopped = scan_upto src in
  check_lines path (checkable_lines path src toks);
  match stopped with
  | None -> ()
  | Some (l, m) ->
      incr issues;
      Printf.printf "%s:%d: %s -- everything above is what was read before that\n" path l m

let () =
  let files = List.tl (Array.to_list Sys.argv) in
  if files = [] then (prerr_endline "usage: indent <file.sl> ..."; exit 2);
  List.iter check_file files;
  if !issues = 0 then (print_endline "no nesting/indentation inconsistencies found"; exit 0)
  else (Printf.printf "%d issue(s) found\n" !issues; exit 1)
