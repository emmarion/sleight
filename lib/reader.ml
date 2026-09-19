type loc = int
type raw = Atom of loc * string | List of loc * raw list

exception Syntax of loc * string

let loc = function Atom (l, _) | List (l, _) -> l

let rec show = function
  | Atom (_, s) -> s
  | List (_, items) -> "(" ^ String.concat " " (List.map show items) ^ ")"

type token = LParen | RParen | Dollar | Word of string

let scan_upto src =
  let n = String.length src in
  let out = ref [] in
  let err line msg = raise (Syntax (line, msg)) in
  let rec skip p i = if i < n && p src.[i] then skip p (i + 1) else i in
  let rec string buf line i =
    if i >= n then err line "unterminated string literal"
    else
      match src.[i] with
      | '"' -> (line, i + 1)
      | '\\' ->
          let e = if i + 1 < n then src.[i + 1] else err line "unterminated string literal" in
          Buffer.add_char buf (match e with 'n' -> '\n' | 't' -> '\t' | '"' | '\\' -> e | _ -> err line ("unknown escape \\" ^ String.make 1 e));
          string buf line (i + 2)
      | c -> Buffer.add_char buf c; string buf (if c = '\n' then line + 1 else line) (i + 1)
  in
  let emit t = out := t :: !out in
  let rec go line i =
    if i < n then
      match src.[i] with
      | '\n' -> go (line + 1) (i + 1)
      | ' ' | '\t' | '\r' -> go line (i + 1)
      | ';' -> go line (skip (( <> ) '\n') i)
      | '(' -> emit (line, i, LParen); go line (i + 1)
      | ')' -> emit (line, i, RParen); go line (i + 1)
      | '"' ->
          let buf = Buffer.create 16 in
          let line, j = string buf line (i + 1) in
          emit (line, i, Word (Literal.quote (Buffer.contents buf))); go line j
      | _ ->
          let j = skip (fun c -> not (String.contains " \t\r\n();" c)) i in
          let w = String.sub src i (j - i) in
          emit (line, i, if w = "$" then Dollar else Word w); go line j
  in
  let stopped = match go 1 0 with () -> None | exception Syntax (l, m) -> Some (l, m) in
  (List.rev !out, stopped)

let scan src =
  match scan_upto src with ts, None -> ts | _, Some (l, m) -> raise (Syntax (l, m))

let tokenize src = List.map (fun (l, _, t) -> (l, t)) (scan src)

(* [read_items] reads until the enclosing form's terminator, which it leaves in place;
   a [$] form ends at that same terminator (DESIGN.md section 2). *)
let parse src =
  let toks = ref (tokenize src) in
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
         | LParen, _ -> raise (Syntax (l, "missing )"))
         | _, None -> raise (Syntax (l, "missing ) after $"))
         | _ -> ());
        read_items (List (l, items) :: acc)
    | Some (l, Word w) -> advance (); read_items (Atom (l, w) :: acc)
  in
  let items = read_items [] in
  match peek () with Some (l, _) -> raise (Syntax (l, "unexpected )")) | None -> items
