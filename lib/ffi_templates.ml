(* The extraction templates of lib/ffi_templates.txt (ASSUMPTIONS 133), parsed into their holes once. *)

type hole = Scrut | Body of int | Field of int * int | Arg of int | Temp of int
type piece = Lit of string | Hole of hole
type key = Match of string | Build of string * int | Fn of string

let hole h =
  let n = String.length h in
  let num s = int_of_string_opt s in
  let rest = if n > 1 then String.sub h 1 (n - 1) else "" in
  match h.[0] with
  | 's' when h = "s" -> Scrut
  | 'b' when num rest <> None -> Body (Option.get (num rest))
  | 'a' when num rest <> None -> Arg (Option.get (num rest))
  | 't' when num rest <> None -> Temp (Option.get (num rest))
  | 'f' -> (
      match List.map num (String.split_on_char '.' rest) with
      | [ Some i; Some j ] -> Field (i, j)
      | _ -> failwith ("malformed template hole {" ^ h ^ "}"))
  | _ -> failwith ("malformed template hole {" ^ h ^ "}")

let pieces text =
  let n = String.length text in
  let rec go i acc =
    if i >= n then List.rev acc
    else
      match String.index_from_opt text i '{' with
      | None -> List.rev (Lit (String.sub text i (n - i)) :: acc)
      | Some j ->
          let k = match String.index_from_opt text j '}' with Some k -> k | None -> failwith "unclosed template hole" in
          let acc = if j > i then Lit (String.sub text i (j - i)) :: acc else acc in
          go (k + 1) (Hole (hole (String.sub text (j + 1) (k - j - 1))) :: acc)
  in
  go 0 []

let table =
  lazy
    (List.filter_map
       (fun line ->
         let line = String.trim line in
         if line = "" || line.[0] = ';' then None
         else
           let i = match String.index_opt line ':' with Some i -> i | None -> failwith ("malformed template line: " ^ line) in
           let key =
             match String.split_on_char ' ' (String.sub line 0 i) with
             | [ "match"; t ] -> Match t
             | [ "build"; t; n ] -> Build (t, int_of_string n)
             | [ "fn"; f ] -> Fn f
             | _ -> failwith ("malformed template line: " ^ line)
           in
           Some (key, pieces (String.trim (String.sub line (i + 1) (String.length line - i - 1)))))
       (String.split_on_char '\n' Ffi_templates_source.source))

let find key = List.assoc_opt key (Lazy.force table)

let outcomes ps = List.exists (function Hole (Body _) -> true | _ -> false) ps

let reads ?(results = false) what noun n ps =
  let count h = List.length (List.filter (( = ) (Hole h)) ps) in
  for j = 0 to n - 1 do if count (Arg j) = 0 then Printf.ksprintf failwith "%s must read {a%d}" what j done;
  List.iter
    (function
      | Hole (Arg j) when j >= n -> Printf.ksprintf failwith "%s reads {a%d}, beyond its %s" what j noun
      | Hole (Body i) when results && count (Body i) > 1 -> Printf.ksprintf failwith "%s must fill {b%d} at most once" what i
      | Hole (Body _ | Field _) when results -> ()
      | Hole (Scrut | Body _ | Field _) -> Printf.ksprintf failwith "%s takes only {a} and {t} holes" what
      | _ -> ())
    ps

(* Against the shape [ns], the many-field arities of the type's constructors: a match fills each body and
   each field binder exactly once and no hole beyond the shape; a build reads each argument. *)
let check name ns =
  let err fmt = Printf.ksprintf failwith fmt in
  let count h ps = List.length (List.filter (( = ) (Hole h)) ps) in
  let arity i = if i < List.length ns then List.nth ns i else err "template for %s names constructor %d, which it has not" name i in
  (match find (Match name) with
   | None -> ()
   | Some ps ->
       List.iteri
         (fun i n ->
           if count (Body i) ps <> 1 then err "the match template for %s must fill {b%d} exactly once" name i;
           for j = 0 to n - 1 do if count (Field (i, j)) ps <> 1 then err "the match template for %s must bind {f%d.%d} exactly once" name i j done)
         ns;
       List.iter
         (function
           | Hole (Body i) -> ignore (arity i)
           | Hole (Field (i, j)) -> if j >= arity i then err "the match template for %s binds {f%d.%d}, beyond the constructor's fields" name i j
           | Hole (Arg _) -> err "the match template for %s takes no {a} hole" name
           | _ -> ())
         ps);
  List.iteri (fun i n -> Option.iter (reads (Printf.sprintf "the build template for %s %d" name i) "fields" n) (find (Build (name, i)))) ns

let check_fn name n = Option.iter (reads ~results:true ("the template for " ^ name) "arguments" n) (find (Fn name))

let fill ps ~scrut ~temp ~field ~body ~arg =
  String.concat ""
    (List.map
       (function
         | Lit s -> s
         | Hole Scrut -> scrut ()
         | Hole (Temp k) -> temp k
         | Hole (Field (i, j)) -> field i j
         | Hole (Body i) -> body i
         | Hole (Arg i) -> arg i)
       ps)

let is_name e = e <> "" && String.for_all (fun c -> c = '_' || c = '\'' || (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9')) e
