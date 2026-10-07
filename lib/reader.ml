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

type token = LParen | RParen | Dollar | Word of string | Pragma of raw list

let unterminated = "unterminated string literal"

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
    if i >= n then err (at line bol i) unterminated
    else
      match src.[i] with
      | '"' -> (line, bol, i + 1)
      | '\\' ->
          let e = if i + 1 < n then src.[i + 1] else err (at line bol i) unterminated in
          Buffer.add_char buf (match e with 'n' -> '\n' | 't' -> '\t' | '"' | '\\' -> e | _ -> err (at line bol i) ("unknown escape \\" ^ String.make 1 e));
          string buf line bol (i + 2)
      | '\n' -> Buffer.add_char buf '\n'; string buf (line + 1) (i + 1) (i + 1)
      | c -> Buffer.add_char buf c; string buf line bol (i + 1)
  in
  let emit t = out := t :: !out in
  let blank c = c = ' ' || c = '\t' || c = '\r' in
  let rec pragma line bol i k =
    let i = skip blank i in
    let j = skip (( <> ) '\n') i in
    let j = if k = 0 then j else skip (fun c -> not (blank c || c = '\n')) i in
    if i >= j then [] else Atom (at line bol i, String.trim (String.sub src i (j - i))) :: (if k = 0 then [] else pragma line bol j (k - 1))
  in
  let rec go line bol i =
    if i < n then
      match src.[i] with
      | '\n' -> go (line + 1) (i + 1) (i + 1)
      | ' ' | '\t' | '\r' -> go line bol (i + 1)
      | ';' when i + 1 < n && src.[i + 1] = '!' ->
          let words = match pragma line bol (i + 2) 2 with Atom (_, "warn") :: _ as ws -> ws | _ -> pragma line bol (i + 2) 3 in
          emit (at line bol i, i, Pragma words); go line bol (skip (( <> ) '\n') i)
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

(* A parenthesis a file gets wrong is found faster with bin/shape than from the one position a message names. *)
let shape_notes = ref true

let shape_note path =
  Printf.sprintf "%s: note: `bin/shape` lists where each form of this file opens and closes, `dune exec bin/shape.exe -- <file>`, and with `--closers` what each run of `)` closes" path

type region = { name : string; from : loc; until : loc option; mutable used : bool }

let regions : (string, region list) Hashtbl.t = Hashtbl.create 8
let before a b = (a.line, a.col) < (b.line, b.col)
let covers r l = not (before l r.from) && match r.until with Some u -> before l u | None -> true

(* [read_items] reads until the enclosing form's terminator, which it leaves in place;
   a [$] form ends at that same terminator (DESIGN.md section 2). [shape] false leaves out the note on a
   parenthesis error, where the indentation check has already written it. *)
let parse ?(shape = true) file src =
  let toks = ref (tokenize file src) in
  let peek () = match !toks with [] -> None | t :: _ -> Some t in
  let advance () = toks := List.tl !toks in
  let paren l m = Syntax (l, if shape && !shape_notes then m ^ "\n" ^ shape_note (where "-" { l with line = 0 }) else m) in
  let opened = ref [] and closed = ref [] in
  let suppression l w = function
    | Atom (_, "warn") :: Atom (_, name) :: _ -> (
        match (w, List.assoc_opt name !opened) with
        | "suppress", None -> opened := (name, l) :: !opened
        | "suppress", Some first -> raise (Syntax (l, Printf.sprintf "`;! suppress warn` for `%s` is already open\n%s: note: opened here" name (where "-" first)))
        | _, Some from -> opened := List.remove_assoc name !opened; closed := { name; from; until = Some l; used = false } :: !closed
        | _, None -> raise (Syntax (l, Printf.sprintf "`;! restore warn` for `%s` has no open `;! suppress warn`" name)))
    | _ -> raise (Syntax (l, Printf.sprintf "`;! %s` takes `warn NAME`" w))
  in
  let rec read_items ?(top = false) acc =
    match peek () with
    | None | Some (_, RParen) -> List.rev acc
    | Some (l, Pragma (Atom (_, (("suppress" | "restore") as w)) :: rest)) -> advance (); suppression l w rest; read_items ~top acc
    | Some (_, Pragma (Atom (wl, w) :: _)) when w <> "warn" -> raise (Syntax (wl, Printf.sprintf "unknown pragma `%s`" w))
    | Some (l, Pragma []) -> raise (Syntax (l, "a pragma needs a word after `;!`"))
    | Some (l, Pragma words) ->
        if not top then raise (Syntax (l, "`;! warn` must be written between top-level forms"));
        advance (); read_items ~top (List (l, Atom (l, ";!") :: words) :: acc)
    | Some (l, ((LParen | Dollar) as opener)) ->
        advance ();
        let items = read_items [] in
        (match (opener, peek ()) with
         | LParen, Some (_, RParen) -> advance ()
         | LParen, _ -> raise (paren l "missing `)`")
         | _, None -> raise (paren l "missing `)` after `$`")
         | _ -> ());
        read_items ~top (List (l, items) :: acc)
    | Some (l, Word w) -> advance (); read_items ~top (Atom (l, w) :: acc)
  in
  let items = read_items ~top:true [] in
  (match peek () with Some (l, _) -> raise (paren l "unexpected `)`") | None -> ());
  let unclosed = List.map (fun (name, from) -> { name; from; until = None; used = false }) !opened in
  Hashtbl.replace regions file (List.sort (fun a b -> compare (a.from.line, a.from.col) (b.from.line, b.from.col)) (!closed @ unclosed));
  items
