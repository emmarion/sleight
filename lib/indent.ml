(* indent.ml -- checks that a .sl file's indentation tracks its paren nesting.

   Not part of the language: a claim the source makes about itself, which the
   driver checks and warns about (bin/indent.ml runs it alone). It reads
   Reader.scan_upto's tokens rather than re-scanning bytes, so it skips
   comments and strings exactly the way the real reader does, and it runs
   before parsing, so a file the reader goes on to refuse is still reported
   on -- which is the case it is most wanted for.

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

   A line is the line a token's first character sits on, read off the token's
   offset rather than off the line the scanner recorded for it, the two
   differing for a string literal spanning lines. Nesting never falls below
   zero: a ) with nothing open is reported where it sits and leaves the depth
   alone, so the nesting the lines after it are checked against is still the
   count of forms actually open.

   $ is not paren nesting and is deliberately not tracked: a $ chain closes
   only at its enclosing form's terminator, so counting it would make the
   common flat-aligned $ chain (self/core.sl's sp-table)
   look like it plunges one level deeper on every line, which is worse than
   ignoring it. Blank lines and comment-only lines carry no tokens and are
   silently skipped, matching the reader.

   The one shape it misreads is the other side of that $ rule: a form
   introduced by $ whose arguments sit on more indented lines below it
   reads as a level that never opened, since $ emits no token. Writing
   such a form with parens appears to be the cheaper side to fix, the
   flat-aligned chain above having no such alternative. *)

open Reader

(* An issue whose location is the file's [nowhere] is the file's as a whole rather than one line's,
   and [Reader.where] then names the file alone. A [note] is a second location the message before it
   talks about: every one of these rules is a comparison between two lines, and the line compared
   against is worth naming rather than describing. *)
type issue = { at : loc; note : bool; msg : string }

let show { at; note; msg } = Printf.sprintf "%s: %s: %s\n" (Reader.where "-" at) (if note then "note" else "warning") msg

type checkable = { pos : loc; indent : int; nesting : int }

(* One line is "checkable" when a token starts on it; its indent is that
   token's column, and its nesting is the paren depth in effect just before
   that token -- i.e. before the line's own characters are read. *)
let checkable_lines report src toks =
  let depth = ref 0 and cur = ref Z.zero and out = ref [] in
  List.iter
    (fun (l, off, tok) ->
       if not (Z.equal l.line !cur) then begin
         cur := l.line;
         let indent = Z.to_int l.col - 1 in
         let bol = off - indent in
         if String.exists (( = ) '\t') (String.sub src bol (off - bol)) then
           report { at = l; note = false; msg = "indentation uses a tab, not spaces only" };
         out := { pos = l; indent; nesting = !depth } :: !out
       end;
       match tok with
       | LParen -> incr depth
       | RParen -> if !depth > 0 then decr depth
       | Dollar | Word _ | Pragma _ -> ())
    toks;
  List.rev !out

(* The indentation/nesting stack, head = innermost: each level with the line that opened it, which is the
   line a later one is compared against and so the one its note names. *)
let check_lines report lines =
  let stack = ref [] in
  List.iter
    (fun { pos = l; indent = i; nesting = n } ->
       let say el note fmt =
         Printf.ksprintf (fun m -> report { at = l; note = false; msg = m }; report { at = el; note = true; msg = note }) fmt
       in
       match !stack with
       | [] -> stack := [ (l, i, n) ]
       | (el, top_i, top_n) :: _ when i = top_i ->
           if n <> top_n then
             say el "the previous line at this indentation"
               "same indentation (%d) as the previous checked line but nesting is %d, expected %d (matching that line)" i n top_n;
           stack := (l, i, n) :: List.tl !stack
       | (el, top_i, top_n) :: _ when i > top_i ->
           if n <= top_n then
             say el "the line before it"
               "indentation increased (%d -> %d) but nesting did not increase (%d -> %d)" top_i i top_n n;
           stack := (l, i, n) :: !stack
       | _ ->
           let rec pop s =
             match s with
             | (el, ei, en) :: rest when ei > i ->
                 if not (en > n) then
                   say el "the line at that indentation"
                     "dedented past indentation %d (nesting %d), but this line's nesting is %d (expected less than %d)" ei en n en;
                 pop rest
             | _ -> s
           in
           let remaining = pop !stack in
           List.iter
             (fun (el, ei, en) ->
                if ei < i && not (en < n) then
                  say el "that enclosing line"
                    "dedented to indentation %d, but an enclosing line at indentation %d has nesting %d, not less than this line's %d" i ei en n)
             remaining;
           (match remaining with
            | (el, ei, en) :: rest when ei = i ->
                if en <> n then
                  say el "the earlier line it matches"
                    "dedented back to indentation %d, matching an earlier line, but nesting is %d there vs %d here" i en n;
                stack := (l, i, n) :: rest
            | _ -> stack := (l, i, n) :: remaining))
    lines

(* Where each form still open at the end was opened, innermost first, and the first ) that closed more than
   was open. A file the reader cannot close is the case this tool is most wanted for, so neither is left to
   the nesting rules: they read relative depth and would pass a file whose indentation is consistent and
   whose forms never close. Naming the openings rather than counting them says where each missing ) goes,
   which is what a reader's "missing )" at the end of the file does not. *)
let balance toks =
  List.fold_left
    (fun (opens, surplus) (l, _, tok) ->
       match tok with
       | LParen -> (l :: opens, surplus)
       | RParen -> (match opens with _ :: rest -> (rest, surplus) | [] -> ([], (if surplus = None then Some l else surplus)))
       | Dollar | Word _ | Pragma _ -> (opens, surplus))
    ([], None) toks

(* The issues, in line order, and where the lexer stopped if it could not finish the file. *)
let issues path src =
  let toks, stopped = scan_upto path src in
  let toks = List.filter (function _, _, Pragma _ -> false | _ -> true) toks in
  let acc = ref [] in
  let report i = acc := i :: !acc in
  check_lines report (checkable_lines report src toks);
  let opens, surplus = balance toks in
  Option.iter (fun l -> report { at = l; note = false; msg = "a `)` here closes more than is open (surplus `)`)" }) surplus;
  List.iteri
    (fun k l -> report { at = l; note = k > 0; msg = (if k = 0 then "this form is never closed" else "and this one") })
    opens;
  (List.rev !acc, stopped)

(* Whether it warned, and so wrote the note on bin/shape, which the reader's error then need not repeat. *)
let warn path src =
  let found = fst (issues path src) in
  List.iter (fun i -> !Env.warn (show i)) found;
  if found <> [] && !Reader.shape_notes then !Env.warn (Reader.shape_note path ^ "\n");
  found <> []
