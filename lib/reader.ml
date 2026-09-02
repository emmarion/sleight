type loc = int
type raw = Atom of loc * string | List of loc * raw list

exception Syntax of loc * string

let loc = function Atom (l, _) | List (l, _) -> l

let rec show = function
  | Atom (_, s) -> s
  | List (_, items) -> "(" ^ String.concat " " (List.map show items) ^ ")"

type token = LParen | RParen | Dollar | Word of string

let tokenize src =
  let n = String.length src in
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
  let rec go line i acc =
    if i >= n then List.rev acc
    else
      match src.[i] with
      | '\n' -> go (line + 1) (i + 1) acc
      | ' ' | '\t' | '\r' -> go line (i + 1) acc
      | ';' -> go line (skip (( <> ) '\n') i) acc
      | '(' -> go line (i + 1) ((line, LParen) :: acc)
      | ')' -> go line (i + 1) ((line, RParen) :: acc)
      | '"' ->
          let buf = Buffer.create 16 in
          let line, j = string buf line (i + 1) in
          go line j ((line, Word (Literal.quote (Buffer.contents buf))) :: acc)
      | _ ->
          let j = skip (fun c -> not (String.contains " \t\r\n();" c)) i in
          let w = String.sub src i (j - i) in
          go line j ((line, if w = "$" then Dollar else Word w) :: acc)
  in
  go 1 0 []

(* [read_items] reads until the enclosing form's terminator, which it leaves in place;
   a [$] form ends at that same terminator (DESIGN.md section 2). *)
let parse src =
  let toks = ref (tokenize src) in
  let peek () = match !toks with [] -> None | t :: _ -> Some t in
  let advance () = toks := List.tl !toks in
  let rec read_items acc =
    match peek () with
    | None | Some (_, RParen) -> List.rev acc
    | Some (l, LParen) ->
        advance ();
        let items = read_items [] in
        (match peek () with
         | Some (_, RParen) -> advance ()
         | _ -> raise (Syntax (l, "missing )")));
        read_items (List (l, items) :: acc)
    | Some (l, Dollar) ->
        advance ();
        let items = read_items [] in
        if peek () = None then raise (Syntax (l, "missing ) after $"));
        read_items (List (l, items) :: acc)
    | Some (l, Word w) -> advance (); read_items (Atom (l, w) :: acc)
  in
  let items = read_items [] in
  match peek () with Some (l, _) -> raise (Syntax (l, "unexpected )")) | None -> items
