(* A position is where a token's first character sits, in the file it was read from, which a `;! file`
   pragma names: what every message a session writes points at (ASSUMPTIONS 194). [nowhere] is the
   location an error carries when it is raised where none is at hand, for an enclosing form to fill in. *)
type loc = Ffi_core.loc = At of { file : string; line : Z.t; col : Z.t } | NoLoc | Unknown

type name = Ffi_core.name = Src of string | Gen of Z.t * string
type raw = Ffi_core.raw = Atom of loc * name | Handle of loc * int * Ffi_core.reading * Ffi_core.mult * Obj.t | Wild of loc | Nat of loc * Z.t | Char of loc * int | Str of loc * string | List of loc * raw list

exception Syntax of loc * string

let nowhere = Unknown
let placed = function At _ -> true | NoLoc | Unknown -> false
let where fallback = function At { file; line; col } -> Printf.sprintf "%s:%s:%s" file (Z.to_string line) (Z.to_string col) | Unknown -> fallback | NoLoc -> ""
let file_of = function At { file; _ } -> file | NoLoc | Unknown -> ""
let label w label = if w = "" then label else w ^ ": " ^ label
let labelled fallback l = label (where fallback l)

let loc = function Atom (l, _) | Handle (l, _, _, _, _) | Wild l | Nat (l, _) | Char (l, _) | Str (l, _) | List (l, _) -> l

let handle_name = ref (fun x -> string_of_int x)

let rec show = function
  | Atom (_, s) -> Literal.name s
  | Handle (_, x, Ffi_core.MintedIs, _, _) -> !handle_name x
  | Handle (_, _, Ffi_core.MintedType, _, _) -> "_"
  | Wild _ -> "_"
  | Nat (_, z) -> Z.to_string z
  | Char (_, c) -> Ffi_core.lit_char c
  | Str (_, s) -> Ffi_core.lit_string s
  | List (_, items) -> "(" ^ String.concat " " (List.map show items) ^ ")"

type token = LParen | RParen | Dollar | Item of raw | Invalid of string | Pragma of raw list

let unterminated = "unterminated string literal"

type file = { path : string; src : string; name : string; toks : (loc * int * token) list; stopped : (loc * string) option }

(* The files a source holds (DESIGN.md section 4): a `;! file` pragma ends the one being read and starts the
   one it names, its lines counted from 1 on the line after the pragma. [bol] is the offset the current
   line starts at, so a token's column is its own offset from there. A string literal's token is placed at
   its opening quote, the line its own rather than the line it closes on, which is what makes a position
   the start of the token it names; an unterminated one is reported there too. *)
let files path src =
  let n = String.length src in
  let out = ref [] and finished = ref [] and name = ref path in
  let at line bol i = At { file = !name; line = Z.of_int line; col = Z.of_int (i - bol + 1) } in
  let err l msg = raise (Syntax (l, msg)) in
  let cut stopped = finished := { path; src; name = !name; toks = List.rev !out; stopped } :: !finished; out := [] in
  let rec skip p i = if i < n && p src.[i] then skip p (i + 1) else i in
  let rec string opened buf line bol i =
    if i >= n then err opened unterminated
    else
      match src.[i] with
      | '"' -> (line, bol, i + 1)
      | '\\' ->
          let e = if i + 1 < n then src.[i + 1] else err opened unterminated in
          let hex = i + 3 < n && e = 'x' && String.for_all (function '0' .. '9' | 'a' .. 'f' | 'A' .. 'F' -> true | _ -> false) (String.sub src (i + 2) 2) in
          Buffer.add_char buf (match e with 'n' -> '\n' | 't' -> '\t' | '"' | '\\' -> e | 'x' when hex -> Char.chr (int_of_string ("0x" ^ String.sub src (i + 2) 2)) | _ -> err (at line bol i) ("unknown escape \\" ^ String.make 1 e));
          string opened buf line bol (i + if hex then 4 else 2)
      | '\n' -> Buffer.add_char buf '\n'; string opened buf (line + 1) (i + 1) (i + 1)
      | c -> Buffer.add_char buf c; string opened buf line bol (i + 1)
  in
  let emit t = out := t :: !out in
  let item l w =
    if w = "_" then Item (Wild l)
    else if String.starts_with ~prefix:"__" w then Invalid (Printf.sprintf "`%s` begins with `__`, which is reserved for the compilers' messages; write it `%s`" w (Literal.spell_name w))
    else match Literal.classify w with
      | `Name -> Item (Atom (l, Src w))
      | `Lit (Literal.Numeral z) -> Item (Nat (l, z))
      | `Lit (Literal.Char c) -> Item (Char (l, c))
      | `Lit (Literal.Str s) -> Item (Str (l, s))
      | `Bad m -> Invalid m in
  let blank c = c = ' ' || c = '\t' || c = '\r' in
  let rec pragma ?(quoted = false) line bol i k =
    let i = skip blank i in
    let j = skip (( <> ) '\n') i in
    let literal =
      if k > 0 && i + 1 < n && src.[i] = '#' && src.[i + 1] = '"' then Some ((fun l b -> Atom (l, Src b)), i + 2)
      else if k > 0 && quoted && i < n && src.[i] = '"' then Some ((fun l b -> Str (l, b)), i + 1)
      else None in
    match literal with
    | Some (make, start) ->
      let buf = Buffer.create 16 in
      let line', _, j = string (at line bol i) buf line bol start in
      if line' <> line then err (at line bol i) "a pragma ends with its line";
      make (at line bol i) (Buffer.contents buf) :: pragma ~quoted line bol j (k - 1)
    | None ->
    let j = if k = 0 then j else skip (fun c -> not (blank c || c = '\n')) i in
    if i >= j then [] else if k = 0 then [ Atom (at line bol i, Src (String.trim (String.sub src i (j - i)))) ] else Atom (at line bol i, Src (String.sub src i (j - i))) :: pragma ~quoted line bol j (k - 1)
  in
  let rec go line bol i =
    if i < n then
      match src.[i] with
      | '\n' -> go (line + 1) (i + 1) (i + 1)
      | ' ' | '\t' | '\r' -> go line bol (i + 1)
      | ';' when i + 1 < n && src.[i + 1] = '!' -> (
          let next line = go line bol (skip (( <> ) '\n') i) in
          match pragma line bol (i + 2) 2 with
          | Atom (_, Src "warn") :: _ as ws -> emit (at line bol i, i, Pragma ws); next line
          | Atom (_, Src "file") :: _ -> (
              match pragma ~quoted:true line bol (i + 2) 3 with
              | [ _; Str (_, f) ] when f <> "" -> cut None; name := f; next 0
              | _ -> err (at line bol i) "`;! file` takes one non-empty string literal, the file's name")
          | _ -> emit (at line bol i, i, Pragma (pragma line bol (i + 2) 3)); next line)
      | ';' -> go line bol (skip (( <> ) '\n') i)
      | '(' -> emit (at line bol i, i, LParen); go line bol (i + 1)
      | ')' -> emit (at line bol i, i, RParen); go line bol (i + 1)
      | '"' -> literal (fun l b -> Str (l, b)) line bol i (i + 1)
      | '#' when i + 1 < n && src.[i + 1] = '"' -> literal (fun l b -> Atom (l, Src b)) line bol i (i + 2)
      | _ ->
          let j = skip (fun c -> not (String.contains " \t\r\n();" c)) i in
          let w = String.sub src i (j - i) in
          emit (at line bol i, i, if w = "$" then Dollar else item (at line bol i) w); go line bol j
  and literal make line bol i start =
    let buf = Buffer.create 16 in
    let opened = at line bol i in
    let line, bol, j = string opened buf line bol start in
    emit (opened, i, Item (make opened (Buffer.contents buf))); go line bol j
  in
  cut (match go 1 0 0 with () -> None | exception Syntax (l, m) -> Some (l, m));
  List.rev !finished

(* What a source holds, read whole, for text that is not a file named on the command line. *)
(* A parenthesis a file gets wrong is found faster with bin/shape than from the one position a message names. *)
let shape_notes = ref true

let shape_note path =
  Printf.sprintf "%s: note: `bin/shape` lists where each form of this file opens and closes, `dune exec bin/shape.exe -- <file>`, and with `--closers` what each run of `)` closes" path

type region = { name : string; from : loc; until : loc option; mutable used : bool }

let regions : (string, region list) Hashtbl.t = Hashtbl.create 8
let coords = function At { line; col; _ } -> (line, col) | NoLoc | Unknown -> (Z.zero, Z.zero)
let compare_loc a b = let (al, ac), (bl, bc) = (coords a, coords b) in match Z.compare al bl with 0 -> Z.compare ac bc | c -> c
let before a b = compare_loc a b < 0
let covers r l = not (before l r.from) && match r.until with Some u -> before l u | None -> true

(* [read_items] reads until the enclosing form's terminator, which it leaves in place;
   a [$] form ends at that same terminator (DESIGN.md section 2). [shape] false leaves out the note on a
   parenthesis error, where the indentation check has already written it. *)
let parse ?(shape = true) (f : file) =
  Option.iter (fun (l, m) -> raise (Syntax (l, m))) f.stopped;
  let toks = ref (List.rev (List.rev_map (fun (l, _, t) -> (l, t)) f.toks)) in
  let peek () = match !toks with [] -> None | t :: _ -> Some t in
  let advance () = toks := List.tl !toks in
  let paren l m = Syntax (l, if shape && !shape_notes then m ^ "\n" ^ shape_note f.path else m) in
  let opened = ref [] and closed = ref [] in
  let suppression l w = function
    | Atom (_, Src "warn") :: Atom (_, Src name) :: _ -> (
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
    | Some (l, Pragma (Atom (_, Src (("suppress" | "restore") as w)) :: rest)) -> advance (); suppression l w rest; read_items ~top acc
    | Some (_, Pragma (Atom (wl, w) :: _)) when w <> Src "warn" -> raise (Syntax (wl, Printf.sprintf "unknown pragma `%s`" (Literal.name w)))
    | Some (l, Pragma []) -> raise (Syntax (l, "a pragma needs a word after `;!`"))
    | Some (l, Pragma words) ->
        if not top then raise (Syntax (l, "`;! warn` must be written between top-level forms"));
        advance (); read_items ~top (List (l, Atom (l, Src ";!") :: words) :: acc)
    | Some (l, ((LParen | Dollar) as opener)) ->
        advance ();
        let items = read_items [] in
        (match (opener, peek ()) with
         | LParen, Some (_, RParen) -> advance ()
         | LParen, _ -> raise (paren l "missing `)`")
         | _, None -> raise (paren l "missing `)` after `$`")
         | _ -> ());
        read_items ~top (List (l, items) :: acc)
    | Some (_, Item r) -> advance (); read_items ~top (r :: acc)
    | Some (l, Invalid m) -> raise (Syntax (l, m))
  in
  let items = read_items ~top:true [] in
  (match peek () with Some (l, _) -> raise (paren l "unexpected `)`") | None -> ());
  let unclosed = List.map (fun (name, from) -> { name; from; until = None; used = false }) !opened in
  Hashtbl.replace regions f.name (List.sort (fun a b -> compare_loc a.from b.from) (!closed @ unclosed));
  items

let read name src = List.concat_map (fun f -> parse f) (files name src)
