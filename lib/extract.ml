open Term
module V = Value
module IntMap = V.IntMap

let sanitize s = String.map (fun c -> if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') then c else '_') s
let var x = Printf.sprintf "v%d%s" x (match Hashtbl.find_opt Env.names x with Some n -> "_" ^ sanitize n | None -> "")
let concat = String.concat
let params vs = if vs = [] then "()" else concat " " (List.map (fun v -> "(" ^ v ^ " : Obj.t)") vs)
let arrows n = concat " -> " (List.init (max n 1) (fun _ -> if n = 0 then "unit" else "Obj.t") @ [ "Obj.t" ])
let args es = if es = [] then "()" else concat " " es
let obj_tuple n = concat " * " (List.init n (fun _ -> "Obj.t"))
let tuple = function [] -> "(Obj.repr ())" | [ e ] -> e | es -> Printf.sprintf "(Obj.repr (%s))" (concat ", " es)
let untuple vs e body =
  match vs with
  | [] -> body
  | [ v ] -> Printf.sprintf "(let %s = %s in %s)" v e body
  | vs -> Printf.sprintf "(let (%s) = (Obj.obj %s : %s) in %s)" (concat ", " vs) e (obj_tuple (List.length vs)) body
let quote s = "\"" ^ String.escaped s ^ "\""

(* An extern type's unwrap into its model's shape and the wrap back (lib/ffi_core.ml's views), over Obj.t. *)
let externs =
  let view name lower args args' = Printf.sprintf "let des_%s v = Obj.repr (Ffi_core.%s_view %s v)\nlet con_%s v = Ffi_core.%s_of %s (Obj.obj v)" name lower args name lower args' in
  [ ("Nat", view "Nat" "nat" "~z:Obj.obj ~nat:Obj.repr" "~z:Obj.obj ~nat:Obj.repr");
    ("Half", view "Half" "half" "~z:Obj.obj ~nat:Obj.repr" "~z:Obj.obj ~nat:Obj.repr");
    ("String", view "String" "str" "~slice:Obj.obj ~u8:Obj.repr ~str:Obj.repr" "~z:Obj.obj ~slice:Obj.obj ~str:Obj.repr") ]

type shape = Ext of string | Tagged of int list | Untagged of int list

let arities adt = List.map (fun c -> c.V.arity) adt.V.ctors
let plain_shape adt = if adt.V.tagged then Tagged (arities adt) else Untagged (arities adt)
let shape adt = if adt.V.ext <> None && !V.use_externs then Ext adt.tname else plain_shape adt

type scope = { capture : V.venv; locals : (id * int) list }

type cx = {
  env : Env.t;
  adts : V.adt list;
  shapes : int list list ref;
  defined : (id, string) Hashtbl.t;
  captured : (V.value * string) list ref;
  seen : (int, (V.value * string option ref) list ref) Hashtbl.t;
  shared : int ref;
  closures : (V.closure * string) list ref;
  out : Buffer.t;
  shows : (term * string * string ref) list ref;
  narrows : ((int list * int list) * string) list ref;
  temps : int ref;
}

(* An extern type's match and builds are its templates (lib/ffi_templates.txt) unless stripped, or where it
   has none, its runtime view; a template's temporaries are numbered per instantiation. *)
let templates = ref true
let template key = if !templates then Ffi_templates.find key else None
let stamp cx = incr cx.temps; !(cx.temps)

let shape_index cx ns =
  let rec go i = function s :: rest -> if s = ns then i else go (i + 1) rest | [] -> cx.shapes := !(cx.shapes) @ [ ns ]; i in
  go 0 !(cx.shapes)
let type_name cx ns = "t" ^ string_of_int (shape_index cx ns)
let ctor_at cx ns i = Printf.sprintf "K%d_%d" (shape_index cx ns) i

let field_names n = List.init n (fun i -> Printf.sprintf "f%d" i)
let fields c = field_names c.V.arity
let spaced parts = Printf.sprintf "\"(\" ^ %s ^ \")\"" (concat " ^ \" \" ^ " parts)
let pattern_at name fs = if fs = [] then name else Printf.sprintf "%s (%s)" name (concat ", " fs)
let pattern cx c fs = pattern_at (ctor_at cx (arities c.V.adt) c.index) fs
let narrow cx ns live =
  let key = (ns, live) in
  match List.assoc_opt key !(cx.narrows) with
  | Some name -> name
  | None ->
      let name = Printf.sprintf "%s_n%d" (type_name cx ns) (List.length !(cx.narrows)) in
      cx.narrows := (key, name) :: !(cx.narrows);
      name

let build cx c es =
  match shape c.V.adt with
  | Ext name -> (
      match template (Ffi_templates.Build (name, c.index)) with
      | None -> Printf.sprintf "(con_%s (Obj.repr (%s)))" name (pattern cx c es)
      | Some ps ->
          let n = stamp cx in
          let args = List.mapi (fun i e -> if Ffi_templates.is_name e then (e, None) else (Printf.sprintf "x%d_a%d" n i, Some e)) es in
          let binds = List.filter_map (fun (x, e) -> Option.map (fun e -> x ^ " = " ^ e) e) args in
          let text = Ffi_templates.fill ps ~scrut:(fun () -> assert false) ~temp:(Printf.sprintf "x%d_t%d" n) ~field:(fun _ _ -> assert false) ~body:(fun _ -> assert false) ~arg:(fun i -> fst (List.nth args i)) in
          if binds = [] then "(" ^ text ^ ")" else Printf.sprintf "(let %s in %s)" (concat " and " binds) text)
  | Tagged _ -> Printf.sprintf "(Obj.repr (%s))" (pattern cx c es)
  | Untagged _ -> tuple es

(* A match over [a]'s constructors: [arms] pair each constructor with its field names and body, [live] the
   discriminants that can occur, which narrows a tagged type so OCaml drops the others; an extern value is
   unwrapped one level first. *)
let dispatch cx a live scrut arms default =
  let cases pat = concat " " (List.map (fun (c, vs, body) -> Printf.sprintf "| %s -> %s" (pat c vs) body) arms) in
  let templated = match shape a with Ext name -> template (Ffi_templates.Match name) | _ -> None in
  let scrut = match shape a with Ext name when templated = None -> Printf.sprintf "(des_%s %s)" name scrut | _ -> scrut in
  match templated with
  | Some ps ->
      let n = stamp cx in
      let live = List.sort_uniq compare live in
      let arm i = List.find_opt (fun (c, _, _) -> c.V.index = i) arms in
      let defaulted = List.filter (fun i -> arm i = None && List.mem i live) (List.init (List.length a.V.ctors) Fun.id) in
      let dflt, thunk =
        match default with
        | Some d when List.length defaulted > 1 -> (Printf.sprintf "(x%d_d ())" n, fun t -> Printf.sprintf "(let x%d_d () = %s in %s)" n d t)
        | Some d -> (d, Fun.id)
        | None -> ("(absurd ())", Fun.id)
      in
      let body i = match arm i with Some (_, _, b) -> b | None -> if List.mem i live then dflt else "(absurd ())" in
      let field i j = match arm i with Some (_, vs, _) -> List.nth vs j | None -> Printf.sprintf "x%d_f%d_%d" n i j in
      let s, bind = if Ffi_templates.is_name scrut then (scrut, Fun.id) else (Printf.sprintf "x%d" n, fun t -> Printf.sprintf "(let x%d = %s in %s)" n scrut t) in
      bind (thunk ("(" ^ Ffi_templates.fill ps ~scrut:(fun () -> s) ~temp:(Printf.sprintf "x%d_t%d" n) ~field ~body ~arg:(fun _ -> assert false) ^ ")"))
  | None ->
  match plain_shape a with
  | Ext _ -> assert false
  | Tagged ns ->
      let live = List.sort_uniq compare live in
      let ty = if List.length live < List.length ns then "yes " ^ narrow cx ns live else type_name cx ns in
      let body = cases (pattern cx) ^ match default with Some d -> " | _ -> " ^ d | None -> "" in
      Printf.sprintf "(match (Obj.obj %s : %s) with %s)" scrut ty (if body = "" then "_ -> ." else body)
  | Untagged _ -> (match arms with [ (_, vs, body) ] -> untuple vs scrut body | [] -> Option.get default | _ -> assert false)

let bucket cx v =
  let h = Hashtbl.hash v in
  match Hashtbl.find_opt cx.seen h with Some b -> b | None -> let b = ref [] in Hashtbl.add cx.seen h b; b

let remember cx v named = let b = bucket cx v in b := (v, named) :: !b

let rec value cx v =
  match v with
  | _ -> (
      let b = bucket cx v in
      match List.find_opt (fun (v', _) -> v' == v) !b with
      | Some (_, { contents = Some name }) -> name
      | Some (_, named) ->
          incr cx.shared;
          let name = Printf.sprintf "shared_%d" !(cx.shared) in
          Buffer.add_string cx.out (Printf.sprintf "let %s : Obj.t = %s\n" name (plain cx v));
          named := Some name;
          name
      | None -> b := (v, ref None) :: !b; plain cx v)

and plain cx = function
  | V.VCtor (c, vs) -> build cx c (List.map (value cx) vs)
  | V.VTuple vs -> tuple (List.map (value cx) vs)
  | V.VExt (_, Int n) -> Printf.sprintf "(Obj.repr (Z.of_string %s))" (quote (Z.to_string n))
  | V.VExt (_, Slice (s, o, l)) -> Printf.sprintf "(Obj.repr ((%s, 0, %d) : Ffi_core.slice))" (quote (String.sub s o l)) l
  | V.VCtorFn c -> var c.cid
  | V.VMatchable adt -> (match shape adt with Ext name -> "(Obj.repr des_" ^ name ^ ")" | _ -> "m_plain")
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
      remember cx v (ref (Some name));
      name

and fn cx scope name f =
  let body =
    match f.V.impl with
    | Some _ when !V.use_externs ->
        let extra = if f.fname = "flatten" then "~rope:Obj.obj ~slice:Obj.obj ~z:Obj.obj ~str:Obj.repr " else "" in
        Printf.sprintf "(Obj.repr (Ffi_core.%s %s%s))" (sanitize f.fname) extra (concat " " (List.map (fun p -> "(Obj.obj " ^ var p ^ ")") f.params))
    | _ -> expr cx scope f.body
  in
  Printf.sprintf "%s %s : Obj.t = %s" name (params (List.map var f.params)) body

and expr cx scope = function
  | V.CVar x when List.mem_assoc x scope.locals -> "(Obj.repr " ^ var x ^ ")"
  | V.CVar x -> (
      match IntMap.find_opt x scope.capture with
      | None -> var x
      | Some (V.VFn cl) -> "(Obj.repr " ^ closure cx cl ^ ")"
      | Some v -> define cx x v)
  | V.CConst v -> value cx v
  | V.CErased -> "(Obj.repr ())"
  | V.CValues cs -> tuple (List.map (expr cx scope) cs)
  | V.CApp (f, es, cc) -> (
      let es = List.map (expr cx scope) es in
      let captured x = if List.mem_assoc x scope.locals then None else IntMap.find_opt x scope.capture in
      let head =
        match f with
        | V.CVar x when List.mem_assoc x scope.locals -> `Fn (var x, List.assoc x scope.locals)
        | V.CVar x -> (match captured x with Some (V.VCtorFn c) -> `Ctor c | Some (V.VFn cl) -> `Fn (closure cx cl, List.length cl.fn.params) | _ -> `Dyn)
        | V.CConst (V.VCtorFn c) -> `Ctor c
        | _ -> `Dyn
      in
      match (cc, head) with
      | V.Ctor, `Ctor c -> build cx c es
      | V.Ctor, _ when es = [] -> expr cx scope f
      | _, `Fn (name, arity) when arity = List.length es -> Printf.sprintf "(%s %s)" name (args es)
      | _ -> Printf.sprintf "((Obj.obj %s : %s) %s)" (expr cx scope f) (arrows (List.length es)) (args es))
  | V.CLet ([], rhs, body) -> Printf.sprintf "(let _ = %s in %s)" (expr cx scope rhs) (expr cx scope body)
  | V.CLet (ids, rhs, body) -> untuple (List.map var ids) (expr cx scope rhs) (expr cx scope body)
  | V.CLetRec (fns, body) ->
      let scope = { scope with locals = List.map (fun (x, f) -> (x, List.length f.V.params)) fns @ scope.locals } in
      Printf.sprintf "(let rec %s in %s)" (concat " and " (List.map (fun (x, f) -> fn cx scope (var x) f) fns)) (expr cx scope body)
  | V.CMatch m ->
      let scrut = expr cx scope m.scrut in
      let a, scrut =
        match m.shape with
        | V.Known a -> (a, scrut)
        | V.Held (code, a) -> (a, if a.tagged then Printf.sprintf "((Obj.obj %s : Obj.t -> Obj.t) %s)" (expr cx scope code) scrut else scrut)
      in
      dispatch cx a m.live scrut (List.map (fun (i, ids, body) -> (V.ctor_at a i, List.map var ids, expr cx scope body)) m.branches) (Option.map (expr cx scope) m.default)
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
  List.iter (fun a -> List.iter (fun c -> Hashtbl.replace defined c.V.cid (var c.cid)) a.V.ctors) adts;
  let closures =
    List.concat_map
      (function
        | Env.Fns fs -> List.filter_map (fun (x, _) -> match IntMap.find_opt x env.values with Some (V.VFn cl) -> Some (cl, var x) | _ -> None) fs
        | Env.Final _ -> [])
      items
  in
  { env; adts; shapes = ref []; defined; captured = ref []; seen = Hashtbl.create 64; shared = ref 0; closures = ref closures; out = Buffer.create 4096; shows = ref []; narrows = ref []; temps = ref 0 }

let all a = List.init (List.length a.V.ctors) Fun.id

(* The type of each shape met, the extern types' unwraps and wraps, and every constructor as its builder. *)
let types cx =
  let builder c =
    let fs = fields c in
    Printf.sprintf "let %s : Obj.t = %s" (var c.V.cid) (if fs = [] then build cx c [] else Printf.sprintf "(Obj.repr (fun %s : Obj.t -> %s))" (params fs) (build cx c fs))
  in
  let extern a = match shape a with Ext name -> Some (List.assoc name externs) | _ -> None in
  let builders = List.concat_map (fun a -> List.map builder a.V.ctors) cx.adts in
  let narrow ((ns, live), name) =
    let decl i n =
      let idx = if List.mem i live then "yes" else "no" in
      if n = 0 then Printf.sprintf "%s : %s %s" (ctor_at cx ns i) idx name else Printf.sprintf "%s : %s -> %s %s" (ctor_at cx ns i) (obj_tuple n) idx name
    in
    Printf.sprintf "type _ %s = %s" name (concat " | " (List.mapi decl ns))
  in
  let decl ns = Printf.sprintf "%s = %s" (type_name cx ns) (concat " | " (List.mapi (fun i n -> let k = ctor_at cx ns i in if n = 0 then k else k ^ " of " ^ obj_tuple n) ns)) in
  concat "\n"
    (List.rev_map narrow !(cx.narrows)
    @ [ (match !(cx.shapes) with [] -> "" | shapes -> "type " ^ concat "\nand " (List.map decl shapes)) ]
    @ List.filter_map extern cx.adts
    @ builders)

(* A Nat as a Z.t: its own integer under the FFI, else the Peano chain counted down one constructor at a time. *)
let nat_z cx =
  let a = (Program.ctor cx.env "Zero").V.adt in
  match shape a with
  | Ext _ -> "(fun (v : Obj.t) -> (Obj.obj v : Z.t))"
  | _ ->
      let arms = [ (Program.ctor cx.env "Zero", [], "n"); (Program.ctor cx.env "Succ", [ "p" ], "(go (Z.succ n) p)") ] in
      Printf.sprintf "(let rec go n (v : Obj.t) = %s in go Z.zero)" (dispatch cx a (all a) "v" arms None)

(* The printer for a literal type, which prints the literal its value reads back from (Literal.spell): a Char and
   a U8 are their Nat (section 38), so neither is unwrapped first. *)
let literal_show cx ty =
  let named name = match (ty, Env.lookup { cx.env with Env.scope = cx.env.Env.prelude } name) with App (Var t, []), Some p -> t = p | _ -> false in
  let string_body () =
    let a = (Program.ctor cx.env "SNil").V.adt in
    match shape a with
    | Ext _ -> "(let (s, o, l) = (Obj.obj v : Ffi_core.slice) in Ffi_core.lit_string (String.sub s o l))"
    | _ ->
        let cons = Printf.sprintf "(Buffer.add_char b (Char.chr (Z.to_int (%s c))); go r)" (nat_z cx) in
        let arms = [ (Program.ctor cx.env "SNil", [], "()"); (Program.ctor cx.env "SCons", [ "c"; "r" ], cons) ] in
        Printf.sprintf "(let b = Buffer.create 16 in let rec go (v : Obj.t) = %s in go v; Ffi_core.lit_string (Buffer.contents b))" (dispatch cx a (all a) "v" arms None)
  in
  if named "Nat" then Some (Printf.sprintf "(Z.to_string (%s v))" (nat_z cx))
  else if named "Char" then Some (Printf.sprintf "(Ffi_core.lit_char (Z.to_int (%s v)))" (nat_z cx))
  else if named "String" then Some (string_body ())
  else None

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
          let env' = Env.merge_opens (Env.unify_force (Env.forcing env') (instantiate (List.rev_map (fun x -> Var x) fids) ret) ty) in
          let many = Elab.non_erased env' fids in
          let shown = List.mapi (fun i x -> Printf.sprintf "%s f%d" (show cx env' (Env.type_of env' x)) i) many in
          let text = if a.V.tagged then spaced (quote c.cname :: shown) else match shown with [] -> "\"_\"" | [ s ] -> s | ss -> spaced ss in
          Some (c, fields c, text)
        with Env.Contradiction _ | Env.Error _ | Not_found -> None
      in
      (body :=
         match literal_show cx ty with
         | Some text -> text
         | None -> (
         match ty with
         | App (Var tid, _) -> (
             match adt_of tid with
             | None -> "\"?\""
             | Some a ->
                 let arms = List.filter_map (branch a) a.V.ctors in
                 dispatch cx a (List.map (fun (c, _, _) -> c.V.index) arms) "v" arms (Some "\"?\""))
         | Fn _ -> "\"<function ?>\""
         | ValCtor _ -> "\"<constructor ?>\""
         | _ -> "\"?\""));
      name

(* The driver's operations on the prelude's values, each direct (lib/driver_core.ml); a String held as the
   FFI's slice converts to and from the host's string directly. *)
let host_conversions =
  "~of_host:(fun s -> Obj.repr ((s, 0, String.length s) : Ffi_core.slice)) ~to_host:(fun v -> let s, o, l = (Obj.obj v : Ffi_core.slice) in String.sub s o l) "
let driver cx =
  let c = Program.ctor cx.env in
  let lam fs body = Printf.sprintf "(fun %s -> %s)" (params fs) body in
  let make n = let fs = fields (c n) in if fs = [] then build cx (c n) [] else lam fs (build cx (c n) fs) in
  let un n arm = let a = (c n).adt in lam [ "v" ] (dispatch cx a (all a) "v" (List.map (fun ct -> let fs = fields ct in (ct, fs, arm ct fs)) a.V.ctors) None) in
  let option n = un n (fun ct fs -> if ct.V.cname = n then Printf.sprintf "(Some (%s))" (concat ", " fs) else "None") in
  let field n = un n (fun _ fs -> List.hd fs) in
  let ops =
    [ ("zero", make "Zero"); ("succ", make "Succ"); ("pred", option "Succ");
      ("u8", make "MkU8"); ("un_u8", field "MkU8"); ("char", make "MkChar"); ("un_char", field "MkChar");
      ("snil", make "SNil"); ("scons", make "SCons"); ("un_str", option "SCons");
      ("some", make "Some"); ("none", make "None"); ("ok", make "Ok"); ("fail", make "Fail"); ("unit", make "MkUnit");
      ("cons", make "Cons"); ("nil", make "Nil"); ("pair", make "MkPair");
      ("is_file", make "IsFile"); ("is_dir", make "IsDir"); ("is_other", make "IsOther"); ("missing", make "Missing");
      ("changed", make "Changed"); ("unchanged", make "Unchanged");
      ("request", un "Exit" (fun ct fs -> Printf.sprintf "(Driver_core.%s (%s))" ct.V.cname (concat ", " fs)));
      ("apply", "(fun (k : Obj.t) (x : Obj.t) -> (Obj.obj k : Obj.t -> Obj.t) x)");
      ("apply0", "(fun (k : Obj.t) -> (Obj.obj k : unit -> Obj.t) ())") ]
  in
  let host = match shape (c "SNil").V.adt with Ext "String" -> host_conversions | _ -> "" in
  Printf.sprintf "let driver = Driver_core.make %s{ %s }\n" host (concat "; " (List.map (fun (k, v) -> "Driver_core." ^ k ^ " = " ^ v) ops))
  ^ {|let flush_to oc s = output_string oc s; flush oc
let program_args = let rec go = function [] -> [] | "--" :: rest -> rest | _ :: rest -> go rest in go (Array.to_list Sys.argv)
let world = { Driver_core.read_rest = (fun () -> In_channel.input_all stdin); read_line = (fun () -> In_channel.input_line stdin); out = flush_to stdout; err = flush_to stderr; args = program_args; env = Sys.getenv_opt; envs = Driver_core.host_envs; cwd = Sys.getcwd; exit; print = print_endline }
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
        | V.VCtorFn c, Program.Plain -> Printf.sprintf "print_endline %s" (quote ("<constructor " ^ c.cname ^ ">"))
        | _, kind -> (
            let e = value cx v in
            match kind with
            | Program.Main -> Printf.sprintf "run_main %s" e
            | Io -> Printf.sprintf "exit (run_io %s)" e
            | Thunk t -> Printf.sprintf "print_endline (%s ((Obj.obj %s : unit -> Obj.t) ()))" (show cx cx.env t) e
            | Plain -> Printf.sprintf "print_endline (%s %s)" (show cx cx.env ty) e)
      in
      Buffer.add_string cx.out (Printf.sprintf "let () = source := %s; %s\n" (quote path) text)

let emit env items =
  let cx = collect env items in
  List.iter (item cx) items;
  let driver = driver cx in
  let shows = List.rev_map (fun (_, name, body) -> Printf.sprintf "%s (v : Obj.t) : string = %s" name !body) !(cx.shows) in
  let types = types cx in
  concat "\n"
    [ "[@@@warning \"-a\"]";
      "module Ffi_core = struct\n" ^ Ffi_core_source.source ^ "\nend";
      "module Driver_core = struct\n" ^ Driver_core_source.source ^ "\nend";
      "let source = ref \"-\"\nlet absurd () = prerr_endline (!source ^ \": runtime error: absurd code reached\"); exit 1";
      "type yes = Yes_ and no = No_\nlet m_plain : Obj.t = Obj.repr (fun (v : Obj.t) : Obj.t -> v)";
      types;
      driver;
      (if shows = [] then "" else "let rec " ^ concat "\nand " shows);
      Buffer.contents cx.out ]
