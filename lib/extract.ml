open Term
module V = Value
module IntMap = V.IntMap

let sanitize s = String.map (fun c -> if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') then c else '_') s
let var x = Printf.sprintf "v%d%s" x (match Hashtbl.find_opt Env.names x with Some n -> "_" ^ sanitize n | None -> "")
let concat = String.concat
let params vs = if vs = [] then "()" else concat " " (List.map (fun v -> "(" ^ v ^ " : Obj.t)") vs)
let arrows n = concat " -> " (List.init (max n 1) (fun _ -> if n = 0 then "unit" else "Obj.t") @ [ "Obj.t" ])
let args es = if es = [] then "()" else concat " " es
let tuple = function [] -> "(Obj.repr ())" | [ e ] -> e | es -> Printf.sprintf "(Obj.repr (%s))" (concat ", " es)
let untuple vs e body =
  match vs with
  | [] -> body
  | [ v ] -> Printf.sprintf "(let %s = %s in %s)" v e body
  | vs -> Printf.sprintf "(let (%s) = (Obj.obj %s : %s) in %s)" (concat ", " vs) e (concat " * " (List.map (fun _ -> "Obj.t") vs)) body
let quote s = "\"" ^ String.escaped s ^ "\""

let externs =
  [ ("Nat", "Ffi_core.peano ~z:Obj.obj ~nat:Obj.repr");
    ("Bin", "Ffi_core.bijective ~z:Obj.obj ~bin:Obj.repr");
    ("String", "Ffi_core.text ~z:Obj.obj ~slice:Obj.obj ~u8:Obj.repr ~str:Obj.repr") ]

type shape = Ext of string | Tagged of int list | Untagged of int list

let shape adt =
  let arities = List.map (fun c -> c.V.arity) adt.V.ctors in
  if adt.V.ext <> None && !V.use_externs then Ext adt.tname else if adt.V.tagged then Tagged arities else Untagged arities
let arities = function Ext _ -> [] | Tagged ns | Untagged ns -> ns

type scope = { capture : V.venv; locals : id list }

type cx = {
  env : Env.t;
  adts : V.adt list;
  shapes : shape list;
  defined : (id, string) Hashtbl.t;
  captured : (V.value * string) list ref;
  seen : (int, V.value * string option ref) Hashtbl.t;
  shared : int ref;
  closures : (V.closure * string) list ref;
  held : shape list ref;
  out : Buffer.t;
  shows : (term * string * string ref) list ref;
  narrows : ((string * int list) * (string * shape)) list ref;
}

let shape_index cx s = let rec go i = function s' :: rest -> if s' = s then i else go (i + 1) rest | [] -> assert false in go 0 cx.shapes
let numbered cx p s = p ^ string_of_int (shape_index cx s)
let type_name cx = numbered cx "t" and mat cx = numbered cx "m_" and con cx = numbered cx "con_" and des cx = numbered cx "des_"
let ctor_at cx s i = Printf.sprintf "%s_%d" (numbered cx "K" s) i
let ctor cx c = ctor_at cx (shape c.V.adt) c.V.index

let field_names n = List.init n (fun i -> Printf.sprintf "f%d" i)
let fields c = field_names c.V.arity
let pair c vs = Printf.sprintf "(%d, [%s])" c.V.index (concat "; " vs)
let case c vs body = Printf.sprintf "| %s -> %s" (pair c vs) body
let spaced parts = Printf.sprintf "\"(\" ^ %s ^ \")\"" (concat " ^ \" \" ^ " parts)
let pattern_at name fs = if fs = [] then name else Printf.sprintf "%s (%s)" name (concat ", " fs)
let pattern cx c fs = pattern_at (ctor cx c) fs
let narrow cx s present =
  let key = (type_name cx s, present) in
  match List.assoc_opt key !(cx.narrows) with
  | Some (name, _) -> name
  | None ->
      let name = Printf.sprintf "%s_n%d" (type_name cx s) (List.length !(cx.narrows)) in
      cx.narrows := (key, (name, s)) :: !(cx.narrows);
      name

let build cx c es =
  match shape c.V.adt with
  | Ext _ as s -> Printf.sprintf "(%s %d [%s])" (con cx s) c.index (concat "; " es)
  | Tagged _ -> Printf.sprintf "(Obj.repr (%s))" (pattern cx c es)
  | Untagged _ -> tuple es

let destruct cx c v =
  match shape c.V.adt with
  | (Ext _ | Tagged _) as s -> Printf.sprintf "(%s %s)" (des cx s) v
  | Untagged _ -> untuple (fields c) v (pair c (fields c))

let rec value cx v =
  match v with
  | _ -> (
      match List.find_opt (fun (v', _) -> v' == v) (Hashtbl.find_all cx.seen (Hashtbl.hash v)) with
      | Some (_, { contents = Some name }) -> name
      | Some (_, named) ->
          incr cx.shared;
          let name = Printf.sprintf "shared_%d" !(cx.shared) in
          Buffer.add_string cx.out (Printf.sprintf "let %s : Obj.t = %s\n" name (plain cx v));
          named := Some name;
          name
      | None -> Hashtbl.add cx.seen (Hashtbl.hash v) (v, ref None); plain cx v)

and plain cx = function
  | V.VCtor (c, vs) -> build cx c (List.map (value cx) vs)
  | V.VTuple vs -> tuple (List.map (value cx) vs)
  | V.VExt (_, Int n) -> Printf.sprintf "(Obj.repr (Z.of_string %s))" (quote (Z.to_string n))
  | V.VExt (_, Slice (s, o, l)) -> Printf.sprintf "(Obj.repr ((%s, 0, %d) : Ffi_core.slice))" (quote (String.sub s o l)) l
  | V.VCtorFn c -> var c.cid
  | V.VMatchable adt ->
      let s = shape adt in
      if not (List.mem s !(cx.held)) then cx.held := s :: !(cx.held);
      mat cx s
  | V.VFn cl -> "(Obj.repr " ^ closure cx cl ^ ")"
  | V.VToken -> "(Obj.repr ())"

and closure cx cl =
  match List.assq_opt cl !(cx.closures) with
  | Some name -> name
  | None ->
      let env = Lazy.force cl.env in
      let peers = IntMap.fold (fun _ v acc -> match v with V.VFn c when c.env == cl.env && not (List.memq c acc) -> c :: acc | _ -> acc) env [] in
      let peers = if List.memq cl peers then peers else cl :: peers in
      let n = List.length !(cx.closures) in
      let named = List.mapi (fun i c -> (c, Printf.sprintf "cl%d_%s" (n + i) (sanitize c.V.fn.fname))) peers in
      cx.closures := named @ !(cx.closures);
      let texts = List.map (fun (c, name) -> fn cx { capture = env; locals = [] } name c.V.fn) named in
      Buffer.add_string cx.out ("let rec " ^ concat "\nand " texts ^ "\n");
      List.assq cl named

and define cx x v =
  let top = IntMap.mem x cx.env.values in
  match if top then Hashtbl.find_opt cx.defined x else List.assq_opt v !(cx.captured) with
  | Some name -> name
  | None ->
      let e = value cx v in
      let name = if top then var x else Printf.sprintf "%s_%d" (var x) (List.length !(cx.captured)) in
      Buffer.add_string cx.out (Printf.sprintf "let %s : Obj.t = %s\n" name e);
      if top then Hashtbl.replace cx.defined x name else cx.captured := (v, name) :: !(cx.captured);
      Hashtbl.add cx.seen (Hashtbl.hash v) (v, ref (Some name));
      name

and fn cx scope name f =
  let body =
    match f.V.impl with
    | Some _ when !V.use_externs ->
        (* An extern over a plain ADT takes that type's destructor or constructor: flatten walks a Rope, nat-cmp
           builds a Cmp. *)
        let plain tname = List.find (fun a -> a.V.tname = tname) cx.adts in
        let extra =
          match f.fname with
          | "flatten" -> Printf.sprintf "~des:%s ~slice:Obj.obj ~z:Obj.obj ~str:Obj.repr " (des cx (shape (plain "Rope")))
          | "nat-cmp" -> Printf.sprintf "~con:%s " (con cx (shape (plain "Cmp")))
          | _ -> ""
        in
        Printf.sprintf "(Obj.repr (Ffi_core.%s %s%s))" (sanitize f.fname) extra (concat " " (List.map (fun p -> "(Obj.obj " ^ var p ^ ")") f.params))
    | _ -> expr cx scope f.body
  in
  Printf.sprintf "%s %s : Obj.t = %s" name (params (List.map var f.params)) body

and expr cx scope = function
  | V.CVar x when List.mem x scope.locals -> "(Obj.repr " ^ var x ^ ")"
  | V.CVar x -> (
      match IntMap.find_opt x scope.capture with
      | None -> var x
      | Some (V.VFn cl) -> "(Obj.repr " ^ closure cx cl ^ ")"
      | Some v -> define cx x v)
  | V.CConst v -> value cx v
  | V.CErased -> "(Obj.repr ())"
  | V.CValues cs -> tuple (List.map (expr cx scope) cs)
  | V.CApp (f, es, V.Ctor) ->
      let es = List.map (expr cx scope) es in
      Printf.sprintf "(let d = (Obj.obj %s : ctor) in d.con d.ix [%s])" (expr cx scope f) (concat "; " es)
  | V.CApp (f, es, _) ->
      let es = List.map (expr cx scope) es in
      Printf.sprintf "((Obj.obj %s : %s) %s)" (expr cx scope f) (arrows (List.length es)) (args es)
  | V.CLet ([], rhs, body) -> Printf.sprintf "(let _ = %s in %s)" (expr cx scope rhs) (expr cx scope body)
  | V.CLet (ids, rhs, body) -> untuple (List.map var ids) (expr cx scope rhs) (expr cx scope body)
  | V.CLetRec (fns, body) ->
      let scope = { scope with locals = List.map fst fns @ scope.locals } in
      Printf.sprintf "(let rec %s in %s)" (concat " and " (List.map (fun (x, f) -> fn cx scope (var x) f) fns)) (expr cx scope body)
  | V.CMatch m -> (
      let branches = List.map (fun (i, ids, body) -> (i, List.map var ids, expr cx scope body)) m.branches in
      let scrut = expr cx scope m.scrut in
      let default = match m.default with Some d -> expr cx scope d | None -> "absurd ()" in
      let one () = match branches with [ (_, vs, body) ] -> (vs, body) | _ -> assert false in
      match m.shape with
      | V.Known a -> (
          let arms arm = concat " " (List.map (fun (i, vs, body) -> arm (V.ctor_at a i) vs body) branches) in
          match shape a with
          | Ext _ as s -> Printf.sprintf "(match %s %s with %s | _ -> %s)" (des cx s) scrut (arms case) default
          | Tagged _ as s ->
              let live = List.sort_uniq compare m.live in
              let cases = arms (fun c vs body -> Printf.sprintf "| %s -> %s" (pattern cx c vs) body) in
              let ty = if List.length live < List.length a.V.ctors then "yes " ^ narrow cx s live else type_name cx s in
              (match m.default with
               | None -> Printf.sprintf "(match (Obj.obj %s : %s) with %s)" scrut ty (if branches = [] then "_ -> ." else cases)
               | Some _ -> Printf.sprintf "(match (Obj.obj %s : %s) with %s | _ -> %s)" scrut ty cases default)
          | Untagged _ -> let vs, body = one () in untuple vs scrut body)
      | V.Held (code, tags) ->
          let arity = match branches with (_, vs, _) :: _ -> List.length vs | [] -> 0 in
          let des = Printf.sprintf "(Obj.obj %s : matchable).mdes %d %s" (expr cx scope code) arity scrut in
          if not tags then
            let vs, body = one () in
            Printf.sprintf "(match snd (%s) with [%s] -> %s | _ -> absurd ())" des (concat "; " vs) body
          else
            let rec chain = function
              | [] -> default
              | (i, vs, body) :: rest ->
                  Printf.sprintf "if i = %d then (match fs with [%s] -> %s | _ -> absurd ()) else %s" i (concat "; " vs) body (chain rest)
            in
            Printf.sprintf "(let (i, fs) = %s in %s)" des (chain branches))
  | V.CAbsurd -> "(absurd ())"


let collect env items =
  let adts = ref [] and defined = Hashtbl.create 64 in
  let adt a = if not (List.memq a !adts) then adts := a :: !adts in
  let rec value = function
    | V.VCtor (c, vs) -> adt c.adt; List.iter value vs
    | V.VTuple vs -> List.iter value vs
    | V.VExt (a, _) -> adt a
    | V.VCtorFn c -> adt c.adt
    | V.VMatchable a -> adt a
    | V.VFn _ | V.VToken -> ()
  and code c =
    (match c with V.CConst v -> value v | V.CLetRec (fs, _) -> List.iter (fun (_, f) -> code f.V.body) fs | _ -> ());
    List.iter code (V.subcodes c)
  in
  IntMap.iter (fun _ v -> value v) env.Env.values;
  List.iter (function Env.Final (v, _, _) -> value v | Env.Fns fs -> List.iter (fun (_, f) -> code f.V.body) fs) items;
  let adts = List.rev !adts in
  let shapes = List.fold_left (fun acc a -> let s = shape a in if List.mem s acc then acc else acc @ [ s ]) [] adts in
  List.iter (fun a -> List.iter (fun c -> Hashtbl.replace defined c.V.cid (var c.cid)) a.V.ctors) adts;
  let closures =
    List.concat_map
      (function
        | Env.Fns fs -> List.filter_map (fun (x, _) -> match IntMap.find_opt x env.values with Some (V.VFn cl) -> Some (cl, var x) | _ -> None) fs
        | Env.Final _ -> [])
      items
  in
  { env; adts; shapes; defined; captured = ref []; seen = Hashtbl.create 64; shared = ref 0; closures = ref closures; held = ref []; out = Buffer.create 4096; shows = ref []; narrows = ref [] }

let types cx =
  let ctors s = List.mapi (fun i n -> (ctor_at cx s i, field_names n)) (arities s) in
  let obj_tuple fs = concat " * " (List.map (fun _ -> "Obj.t") fs) in
  let decl s =
    let body =
      match s with
      | Ext "String" -> "Ffi_core.slice"
      | Ext _ -> "Z.t"
      | Tagged _ -> concat " | " (List.map (fun (k, fs) -> if fs = [] then k else k ^ " of " ^ obj_tuple fs) (ctors s))
      | Untagged [ 0 ] -> "unit"
      | Untagged [ n ] -> obj_tuple (field_names n)
      | Untagged _ -> "Obj.t"
    in
    Printf.sprintf "%s = %s" (type_name cx s) body
  in
  let case_at i fs body = Printf.sprintf "| (%d, [%s]) -> %s" i (concat "; " fs) body in
  let ops s =
    let constructor arm = Printf.sprintf "let %s i args = match (i, args) with %s | _ -> assert false" (con cx s) (concat " " (List.mapi (fun i (k, fs) -> case_at i fs (arm k fs)) (ctors s))) in
    match s with
    | Ext name -> Printf.sprintf "let %s, %s = %s" (con cx s) (des cx s) (List.assoc name externs)
    | Tagged _ ->
        constructor (fun k fs -> Printf.sprintf "(Obj.repr (%s))" (pattern_at k fs))
        ^ Printf.sprintf "\nlet %s v = match (Obj.obj v : %s) with %s" (des cx s) (type_name cx s)
            (concat " " (List.mapi (fun i (k, fs) -> Printf.sprintf "| %s -> (%d, [%s])" (pattern_at k fs) i (concat "; " fs)) (ctors s)))
    | Untagged _ -> constructor (fun _ fs -> tuple fs)
  in
  let descriptor c =
    Printf.sprintf "let %s : Obj.t = Obj.repr { ix = %d; cname = %s; con = %s; des = (fun v -> %s) }" (var c.V.cid) c.index (quote c.cname) (con cx (shape c.adt)) (destruct cx c "v")
  in
  (* The Matchable value of each shape held as one: its destructor, or the fields as they stand. *)
  let matchable s =
    let des =
      match s with
      | Ext _ | Tagged _ -> Printf.sprintf "(fun _ v -> %s v)" (des cx s)
      | Untagged ns ->
          let arm n = let vs = field_names n in
            Printf.sprintf "| %d -> %s" n (untuple vs "v" (Printf.sprintf "(0, [%s])" (concat "; " vs))) in
          Printf.sprintf "(fun arity v -> match arity with %s | _ -> assert false)" (concat " " (List.init (List.fold_left max 0 ns + 1) arm))
    in
    Printf.sprintf "let %s : Obj.t = Obj.repr ({ mdes = %s } : matchable)" (mat cx s) des
  in
  concat "\n"
    (("type " ^ concat "\nand " (List.map decl cx.shapes))
    :: List.map ops cx.shapes
    @ List.concat_map (fun a -> List.map descriptor a.V.ctors) cx.adts
    @ List.map matchable !(cx.held))

let rec show cx env ty =
  let ty = Env.canon env ty in
  let key = map_vars (fun _ t -> match t with Var x when not (IntMap.mem x cx.env.entries) -> Var (-1) | t -> t) 0 ty in
  match List.find_opt (fun (k, _, _) -> equal k key) !(cx.shows) with
  | Some (_, name, _) -> name
  | None ->
      let name = Printf.sprintf "show_%d" (List.length !(cx.shows)) and body = ref "" in
      cx.shows := (key, name, body) :: !(cx.shows);
      let adt_of tid = List.find_opt (fun a -> match a.V.ctors with c :: _ -> (try Elab.tid_of env 0 c.cid = tid with _ -> false) | [] -> false) cx.adts in
      let branch a c =
        try
          let tele, ret = Elab.ctor_type env 0 c.V.cid in
          let env', fids = Elab.open_tele env tele in
          let env' = Env.unify ~force:true env' (instantiate (List.rev_map (fun x -> Var x) fids) ret) ty in
          let many = Elab.non_erased env' fids in
          let shown = List.mapi (fun i x -> Printf.sprintf "%s f%d" (show cx env' (Env.type_of env' x)) i) many in
          let text = if a.V.tagged then spaced (quote c.cname :: shown) else match shown with [] -> "\"_\"" | [ s ] -> s | ss -> spaced ss in
          Some (c, text)
        with Env.Contradiction _ | Env.Error _ | Not_found -> None
      in
      (body :=
         match ty with
         | App (Var tid, _) -> (
             match adt_of tid with
             | None -> "\"?\""
             | Some a -> (
                 let branches = List.filter_map (branch a) a.V.ctors in
                 match shape a with
                 | Untagged _ -> (match branches with (c, text) :: _ -> untuple (fields c) "v" text | [] -> "\"?\"")
                 | s ->
                     Printf.sprintf "match %s v with %s | _ -> \"?\"" (des cx s)
                       (concat " " (List.map (fun (c, text) -> case c (fields c) text) branches))))
         | Fn _ -> "\"<function ?>\""
         | ValCtor _ -> "\"<constructor \" ^ (Obj.obj v : ctor).cname ^ \">\""
         | _ -> "\"?\"");
      name

let prelude_ctor cx name = var (Program.ctor cx.env name).cid

let driver cx =
  let io = (Program.ctor cx.env "Exit").adt in
  Printf.sprintf "let ctor_of = function %s | _ -> assert false\n"
    (concat " " (List.map (fun n -> Printf.sprintf "| %s -> %s" (quote n) (prelude_ctor cx n)) [ "Zero"; "Succ"; "MkU8"; "MkChar"; "SNil"; "SCons"; "Some"; "None"; "Ok"; "Fail"; "MkUnit"; "Cons"; "Nil"; "Exit" ]))
  ^ Printf.sprintf "let io_names = [| %s |]\n" (concat "; " (List.map (fun c -> quote c.V.cname) io.ctors))
  ^ {|let driver =
  Driver_core.make ~build:(fun n args -> let c = (Obj.obj (ctor_of n) : ctor) in c.con c.ix args) ~des:(fun n v -> (Obj.obj (ctor_of n) : ctor).des v)
    ~io_name:(fun i -> io_names.(i)) ~apply:(fun k x -> (Obj.obj k : Obj.t -> Obj.t) x)
let flush_to oc s = output_string oc s; flush oc
let program_args = let rec go = function [] -> [] | "--" :: rest -> rest | _ :: rest -> go rest in go (Array.to_list Sys.argv)
let world = { Driver_core.input = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin); out = flush_to stdout; err = flush_to stderr; args = program_args; exit; print = print_endline }
let run_io = driver.run_io world
let run_main = driver.run_main world
|}

let item cx = function
  | Env.Fns fns ->
      let text = concat "\nand " (List.map (fun (x, f) -> fn cx { capture = cx.env.values; locals = [] } (var x) f) fns) in
      Buffer.add_string cx.out ("let rec " ^ text ^ "\n")
  | Env.Final (v, ty, path) ->
      let text =
        match (v, Program.final cx.env ty) with
        | V.VFn cl, Program.Plain -> Printf.sprintf "print_endline %s" (quote ("<function " ^ cl.fn.fname ^ ">"))
        | _, kind -> (
            let e = value cx v in
            match kind with
            | Program.Main -> Printf.sprintf "run_main %s" e
            | Io -> Printf.sprintf "exit (run_io %s)" e
            | Thunk t -> Printf.sprintf "print_endline (%s ((Obj.obj %s : unit -> Obj.t) ()))" (show cx cx.env t) e
            | Plain -> Printf.sprintf "print_endline (%s %s)" (show cx cx.env ty) e)
      in
      Buffer.add_string cx.out (Printf.sprintf "let () = source := %s; %s\n" (quote path) text)

let narrows cx =
  let one ((_, present), (name, s)) =
    let decl i n =
      let idx = if List.mem i present then "yes" else "no" in
      if n = 0 then Printf.sprintf "%s : %s %s" (ctor_at cx s i) idx name
      else Printf.sprintf "%s : %s -> %s %s" (ctor_at cx s i) (concat " * " (List.init n (fun _ -> "Obj.t"))) idx name
    in
    Printf.sprintf "type _ %s = %s" name (concat " | " (List.mapi decl (arities s)))
  in
  concat "\n" (List.rev_map one !(cx.narrows))

let emit env items =
  let cx = collect env items in
  List.iter (item cx) items;
  let shows = List.rev_map (fun (_, name, body) -> Printf.sprintf "%s (v : Obj.t) : string = %s" name !body) !(cx.shows) in
  concat "\n"
    [ "[@@@warning \"-a\"]";
      "module Ffi_core = struct\n" ^ Ffi_core_source.source ^ "\nend";
      "module Driver_core = struct\n" ^ Driver_core_source.source ^ "\nend";
      "type ctor = { ix : int; cname : string; con : int -> Obj.t list -> Obj.t; des : Obj.t -> int * Obj.t list }";
      "type matchable = { mdes : int -> Obj.t -> int * Obj.t list }";
      "let source = ref \"-\"\nlet absurd () = prerr_endline (!source ^ \": runtime error: absurd code reached\"); exit 1";
      "type yes = Yes_ and no = No_";
      narrows cx;
      types cx;
      driver cx;
      (if shows = [] then "" else "let rec " ^ concat "\nand " shows);
      Buffer.contents cx.out ]
