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
  let toks = ref [] in
  let line = ref 1 in
  let push t = toks := (!line, t) :: !toks in
  let i = ref 0 in
  while !i < n do
    let c = src.[!i] in
    if c = '\n' then (incr line; incr i)
    else if c = ' ' || c = '\t' || c = '\r' then incr i
    else if c = ';' then while !i < n && src.[!i] <> '\n' do incr i done
    else if c = '(' then (push LParen; incr i)
    else if c = ')' then (push RParen; incr i)
    else begin
      let start = !i in
      while !i < n && not (String.contains " \t\r\n();" src.[!i]) do incr i done;
      let w = String.sub src start (!i - start) in
      push (if w = "$" then Dollar else Word w)
    end
  done;
  List.rev !toks

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
