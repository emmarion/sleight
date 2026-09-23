(* A position is where a token's first character sits, named by the file it was read from: what every
   message a session writes points at (ASSUMPTIONS 194). [nowhere] is the location an error carries when
   it is raised where none is at hand, for an enclosing form to fill in. *)
type loc = { file : string; line : int; col : int }

type raw = Atom of loc * string | List of loc * raw list

exception Syntax of loc * string

let nowhere = { file = ""; line = 0; col = 0 }
let placed l = l.line <> 0
let where fallback l =
  let f = if l.file = "" then fallback else l.file in
  if placed l then Printf.sprintf "%s:%d:%d" f l.line l.col else f

let loc = function Atom (l, _) | List (l, _) -> l

let rec show = function
  | Atom (_, s) -> s
  | List (_, items) -> "(" ^ String.concat " " (List.map show items) ^ ")"

type token = LParen | RParen | Dollar | Word of string

(* [bol] is the offset the current line starts at, so a token's column is its own offset from there. A
   string literal's token is placed at its opening quote, the line its own rather than the line it closes
   on, which is what makes a position the start of the token it names. *)
let scan_upto file src =
  let n = String.length src in
  let out = ref [] in
  let at line bol i = { file; line; col = i - bol + 1 } in
  let err l msg = raise (Syntax (l, msg)) in
  let rec skip p i = if i < n && p src.[i] then skip p (i + 1) else i in
  let rec string buf line bol i =
    if i >= n then err (at line bol i) "unterminated string literal"
    else
      match src.[i] with
      | '"' -> (line, bol, i + 1)
      | '\\' ->
          let e = if i + 1 < n then src.[i + 1] else err (at line bol i) "unterminated string literal" in
          Buffer.add_char buf (match e with 'n' -> '\n' | 't' -> '\t' | '"' | '\\' -> e | _ -> err (at line bol i) ("unknown escape \\" ^ String.make 1 e));
          string buf line bol (i + 2)
      | '\n' -> Buffer.add_char buf '\n'; string buf (line + 1) (i + 1) (i + 1)
      | c -> Buffer.add_char buf c; string buf line bol (i + 1)
  in
  let emit t = out := t :: !out in
  let rec go line bol i =
    if i < n then
      match src.[i] with
      | '\n' -> go (line + 1) (i + 1) (i + 1)
      | ' ' | '\t' | '\r' -> go line bol (i + 1)
      | ';' -> go line bol (skip (( <> ) '\n') i)
      | '(' -> emit (at line bol i, i, LParen); go line bol (i + 1)
      | ')' -> emit (at line bol i, i, RParen); go line bol (i + 1)
      | '"' ->
          let buf = Buffer.create 16 in
          let opened = at line bol i in
          let line, bol, j = string buf line bol (i + 1) in
          emit (opened, i, Word (Literal.quote (Buffer.contents buf))); go line bol j
      | _ ->
          let j = skip (fun c -> not (String.contains " \t\r\n();" c)) i in
          let w = String.sub src i (j - i) in
          emit (at line bol i, i, if w = "$" then Dollar else Word w); go line bol j
  in
  let stopped = match go 1 0 0 with () -> None | exception Syntax (l, m) -> Some (l, m) in
  (List.rev !out, stopped)

let scan file src =
  match scan_upto file src with ts, None -> ts | _, Some (l, m) -> raise (Syntax (l, m))

let tokenize file src = List.map (fun (l, _, t) -> (l, t)) (scan file src)

(* [read_items] reads until the enclosing form's terminator, which it leaves in place;
   a [$] form ends at that same terminator (DESIGN.md section 2). *)
let parse file src =
  let toks = ref (tokenize file src) in
  let peek () = match !toks with [] -> None | t :: _ -> Some t in
  let advance () = toks := List.tl !toks in
  let rec read_items acc =
    match peek () with
    | None | Some (_, RParen) -> List.rev acc
    | Some (l, ((LParen | Dollar) as opener)) ->
        advance ();
        let items = read_items [] in
        (match (opener, peek ()) with
         | LParen, Some (_, RParen) -> advance ()
         | LParen, _ -> raise (Syntax (l, "missing `)`"))
         | _, None -> raise (Syntax (l, "missing `)` after `$`"))
         | _ -> ());
        read_items (List (l, items) :: acc)
    | Some (l, Word w) -> advance (); read_items (Atom (l, w) :: acc)
  in
  let items = read_items [] in
  match peek () with Some (l, _) -> raise (Syntax (l, "unexpected `)`")) | None -> items
