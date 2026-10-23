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

let reads what noun n ps =
  let count h = List.length (List.filter (( = ) (Hole h)) ps) in
  for j = 0 to n - 1 do if count (Arg j) = 0 then Printf.ksprintf failwith "%s must read {a%d}" what j done;
  List.iter
    (function
      | Hole (Arg j) when j >= n -> Printf.ksprintf failwith "%s reads {a%d}, beyond its %s" what j noun
      | Hole (Scrut | Body _ | Field _) -> Printf.ksprintf failwith "%s takes only {a} and {t} holes" what
      | _ -> ())
    ps

(* Against the shape [ns], the many-field arities of the type's constructors: [ps] fills each constructor's body
   exactly once ([every]) or at most once, binds each of its fields as often as it fills its body, and names
   nothing beyond the shape. *)
let arms what ns ~every ps =
  let err fmt = Printf.ksprintf failwith fmt in
  let count h = List.length (List.filter (( = ) (Hole h)) ps) in
  let arity i = if i < List.length ns then List.nth ns i else err "%s names constructor %d, which it has not" what i in
  List.iteri
    (fun i n ->
      let b = count (Body i) in
      if b > 1 || (every && b = 0) then err "%s must fill {b%d} %s" what i (if every then "exactly once" else "at most once");
      for j = 0 to n - 1 do if count (Field (i, j)) <> b then err "%s must bind {f%d.%d} as often as it fills {b%d}" what i j i done)
    ns;
  List.iter
    (function
      | Hole (Body i) -> ignore (arity i)
      | Hole (Field (i, j)) -> if j >= arity i then err "%s binds {f%d.%d}, beyond the constructor's fields" what i j
      | _ -> ())
    ps

let check name ns =
  Option.iter
    (fun ps ->
      let what = "the match template for " ^ name in
      if List.exists (function Hole (Arg _) -> true | _ -> false) ps then failwith (what ^ " takes no {a} hole");
      arms what ns ~every:true ps)
    (find (Match name));
  List.iteri (fun i n -> Option.iter (reads (Printf.sprintf "the build template for %s %d" name i) "fields" n) (find (Build (name, i)))) ns

let check_fn name n decides =
  Option.iter
    (fun ps ->
      let what = "the template for " ^ name in
      match decides with
      | Some ns when outcomes ps -> reads what "arguments" n (List.filter (function Hole (Body _ | Field _) -> false | _ -> true) ps); arms what ns ~every:false ps
      | _ -> reads what "arguments" n ps)
    (find (Fn name))

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
