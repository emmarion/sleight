open Term
module V = Value
module IntMap = V.IntMap

let sanitize s = String.map (fun c -> if (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || (c >= '0' && c <= '9') then c else '_') s
let var x = Printf.sprintf "v%d%s" x (match Hashtbl.find_opt Env.names x with Some n -> "_" ^ sanitize n | None -> "")
let ctor c = Printf.sprintf "C%d_%s" c.V.cid (sanitize c.V.cname)
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
    ("U8", "Ffi_core.bounded ~z:Obj.obj ~nat:Obj.repr ~u8:Obj.repr");
    ("Bin", "Ffi_core.bijective ~z:Obj.obj ~bin:Obj.repr");
    ("String", "Ffi_core.text ~z:Obj.obj ~slice:Obj.obj ~u8:Obj.repr ~str:Obj.repr") ]

type shape = Ext | Tagged | Untagged

let shape adt = if adt.V.ext <> None && !V.use_externs then Ext else if adt.V.tagged then Tagged else Untagged

type cx = {
  env : Env.t;
  adts : V.adt list;
  ctors : (id, V.ctor) Hashtbl.t;
  fns : (id, int) Hashtbl.t;
  globals : (id, unit) Hashtbl.t;
  shows : (term * string * string ref) list ref;
}

let adt_index cx adt = let rec go i = function a :: rest -> if a == adt then i else go (i + 1) rest | [] -> assert false in go 0 cx.adts
let type_name cx adt = Printf.sprintf "t%d_%s" (adt_index cx adt) (sanitize adt.V.tname)
let con cx adt = Printf.sprintf "con_%d" (adt_index cx adt)
let des cx adt = Printf.sprintf "des_%d" (adt_index cx adt)

let fields c = List.init c.V.arity (fun i -> Printf.sprintf "f%d" i)
let pattern c fs = if fs = [] then ctor c else Printf.sprintf "%s (%s)" (ctor c) (concat ", " fs)

let build cx c es =
  match shape c.V.adt with
  | Ext -> Printf.sprintf "(%s %d [%s])" (con cx c.adt) c.index (concat "; " es)
  | Tagged -> Printf.sprintf "(Obj.repr (%s))" (pattern c es)
  | Untagged -> tuple es

let destruct cx c v =
  match shape c.V.adt with
  | Ext | Tagged -> Printf.sprintf "(%s %s)" (des cx c.adt) v
  | Untagged -> Printf.sprintf "(%d, %s)" c.index (untuple (fields c) v (Printf.sprintf "[%s]" (concat "; " (fields c))))

let rec value cx = function
  | V.VCtor (c, vs) -> build cx c (List.map (value cx) vs)
  | V.VTuple vs -> tuple (List.map (value cx) vs)
  | V.VExt (_, Int n) -> Printf.sprintf "(Obj.repr (Z.of_string %s))" (quote (Z.to_string n))
  | V.VExt (_, Slice (s, o, l)) -> Printf.sprintf "(Obj.repr ((%s, 0, %d) : Ffi_core.slice))" (quote (String.sub s o l)) l
  | V.VCtorFn c -> var c.cid
  | V.VFn cl -> failwith ("extraction: cannot embed the closure " ^ cl.fn.fname)
  | V.VToken -> "(Obj.repr ())"

let rec expr cx = function
  | V.CVar x -> (
      if Hashtbl.mem cx.fns x then "(Obj.repr " ^ var x ^ ")"
      else
        match IntMap.find_opt x cx.env.values with
        | Some v when not (Hashtbl.mem cx.globals x) -> value cx v
        | _ -> var x)
  | V.CConst v -> value cx v
  | V.CErased -> "(Obj.repr ())"
  | V.CValues cs -> tuple (List.map (expr cx) cs)
  | V.CApp (f, es, V.Ctor) -> (
      let es = List.map (expr cx) es in
      match static cx f with
      | Some c -> build cx c es
      | None -> Printf.sprintf "(let d = (Obj.obj %s : ctor) in d.con d.ix [%s])" (expr cx f) (concat "; " es))
  | V.CApp (f, es, _) -> (
      let es = List.map (expr cx) es in
      match f with
      | V.CVar g when Hashtbl.mem cx.fns g -> Printf.sprintf "(%s %s)" (var g) (args es)
      | _ -> Printf.sprintf "((Obj.obj %s : %s) %s)" (expr cx f) (arrows (List.length es)) (args es))
  | V.CLet ([], rhs, body) -> Printf.sprintf "(let _ = %s in %s)" (expr cx rhs) (expr cx body)
  | V.CLet (ids, rhs, body) -> untuple (List.map var ids) (expr cx rhs) (expr cx body)
  | V.CLetRec (fns, body) -> Printf.sprintf "(let rec %s in %s)" (concat " and " (List.map (fn cx) fns)) (expr cx body)
  | V.CMatch (s, branches) -> (
      let branch (c, ids, body) = (static cx c, c, List.map var ids, expr cx body) in
      let branches = List.map branch branches in
      match branches with
      | (Some c, _, _, _) :: _ when List.for_all (fun (c, _, _, _) -> c <> None) branches -> (
          let case (c, _, vs, body) = (Option.get c, vs, body) in
          match shape c.adt with
          | Ext ->
              Printf.sprintf "(match %s %s with %s | _ -> absurd ())" (des cx c.adt) (expr cx s)
                (concat " " (List.map (fun (c, vs, body) -> Printf.sprintf "| (%d, [%s]) -> %s" c.V.index (concat "; " vs) body) (List.map case branches)))
          | Tagged ->
              Printf.sprintf "(match (Obj.obj %s : %s) with %s | _ -> absurd ())" (expr cx s) (type_name cx c.adt)
                (concat " " (List.map (fun (c, vs, body) -> Printf.sprintf "| %s -> %s" (pattern c vs) body) (List.map case branches)))
          | Untagged -> (match List.map case branches with [ (_, vs, body) ] -> untuple vs (expr cx s) body | _ -> assert false))
      | _ ->
          let rec chain = function
            | [] -> "absurd ()"
            | (_, c, vs, body) :: rest ->
                Printf.sprintf "let d = (Obj.obj %s : ctor) in if i = d.ix then (match fs with [%s] -> %s | _ -> absurd ()) else %s" (expr cx c) (concat "; " vs) body (chain rest)
          in
          let _, c, _, _ = List.hd branches in
          Printf.sprintf "(let (i, fs) = (Obj.obj %s : ctor).des %s in %s)" (expr cx c) (expr cx s) (chain branches))
  | V.CAbsurd -> "(absurd ())"

and static cx = function V.CVar c -> Hashtbl.find_opt cx.ctors c | V.CConst (V.VCtorFn c) -> Some c | _ -> None

and fn cx (x, f) =
  let body =
    match f.V.impl with
    | Some _ when !V.use_externs ->
        Printf.sprintf "(Obj.repr (Ffi_core.%s %s))" (sanitize f.fname) (concat " " (List.map (fun p -> "(Obj.obj " ^ var p ^ ")") f.params))
    | _ -> expr cx f.body
  in
  Printf.sprintf "%s %s : Obj.t = %s" (var x) (params (List.map var f.params)) body

let collect env items =
  let adts = ref [] and ctors = Hashtbl.create 64 and fns = Hashtbl.create 64 and globals = Hashtbl.create 64 in
  let adt a = if not (List.memq a !adts) then adts := a :: !adts in
  let rec value = function
    | V.VCtor (c, vs) -> adt c.adt; List.iter value vs
    | V.VTuple vs -> List.iter value vs
    | V.VExt (a, _) -> adt a
    | V.VCtorFn c -> adt c.adt
    | V.VFn _ | V.VToken -> ()
  and code = function
    | V.CConst v -> value v
    | V.CValues cs -> List.iter code cs
    | V.CApp (f, cs, _) -> code f; List.iter code cs
    | V.CLet (_, a, b) -> code a; code b
    | V.CLetRec (fs, b) -> List.iter (fun (x, f) -> Hashtbl.replace fns x (List.length f.V.params); code f.body) fs; code b
    | V.CMatch (s, brs) -> code s; List.iter (fun (c, _, b) -> code c; code b) brs
    | V.CVar _ | V.CErased | V.CAbsurd -> ()
  in
  IntMap.iter (fun x v -> value v; match v with V.VCtorFn c -> Hashtbl.replace ctors x c | _ -> ()) env.Env.values;
  List.iter
    (function
      | Env.Let (ids, c) -> List.iter (fun x -> Hashtbl.replace globals x ()) ids; code c
      | Env.Final (c, _) -> code c
      | Env.Fns fs -> List.iter (fun (x, f) -> Hashtbl.replace fns x (List.length f.V.params); Hashtbl.replace globals x (); code f.body) fs)
    items;
  let adts = List.rev !adts in
  List.iter (fun a -> List.iter (fun c -> Hashtbl.replace ctors c.V.cid c; Hashtbl.replace globals c.cid ()) a.V.ctors) adts;
  { env; adts; ctors; fns; globals; shows = ref [] }

let types cx =
  let fields_type c = if c.V.arity = 0 then ctor c else ctor c ^ " of " ^ concat " * " (List.map (fun _ -> "Obj.t") (fields c)) in
  let adt a =
    let body =
      match shape a with
      | Ext -> if a.tname = "String" then "Ffi_core.slice" else "Z.t"
      | Tagged -> concat " | " (List.map fields_type a.ctors)
      | Untagged -> (match a.ctors with [ c ] -> (match c.V.arity with 0 -> "unit" | 1 -> "Obj.t" | n -> concat " * " (List.init n (fun _ -> "Obj.t"))) | _ -> "Obj.t")
    in
    Printf.sprintf "%s = %s" (type_name cx a) body
  in
  let case c built = Printf.sprintf "| (%d, [%s]) -> %s" c.V.index (concat "; " (fields c)) built in
  let ops a =
    match shape a with
    | Ext -> Printf.sprintf "let %s, %s = %s" (con cx a) (des cx a) (List.assoc a.V.tname externs)
    | Tagged ->
        Printf.sprintf "let %s i args = match (i, args) with %s | _ -> assert false\nlet %s v = match (Obj.obj v : %s) with %s" (con cx a)
          (concat " " (List.map (fun c -> case c (Printf.sprintf "(Obj.repr (%s))" (pattern c (fields c)))) a.V.ctors))
          (des cx a) (type_name cx a)
          (concat " " (List.map (fun c -> Printf.sprintf "| %s -> (%d, [%s])" (pattern c (fields c)) c.V.index (concat "; " (fields c))) a.ctors))
    | Untagged -> Printf.sprintf "let %s i args = match (i, args) with %s | _ -> assert false" (con cx a) (concat " " (List.map (fun c -> case c (tuple (fields c))) a.V.ctors))
  in
  let descriptor c =
    Printf.sprintf "let %s : Obj.t = Obj.repr { ix = %d; cname = %s; con = %s; des = (fun v -> %s) }" (var c.V.cid) c.index (quote c.cname) (con cx c.adt) (destruct cx c "v")
  in
  concat "\n" (("type " ^ concat "\nand " (List.map adt cx.adts)) :: List.map ops cx.adts @ List.concat_map (fun a -> List.map descriptor a.V.ctors) cx.adts)

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
          if (Env.entry env c.V.cid).mult = Erased then None
          else
            let tele, ret = Elab.ctor_type env 0 c.cid in
            let env', fids = Elab.open_tele env tele in
            let env' = Env.unify env' (instantiate (List.rev_map (fun x -> Var x) fids) ret) ty in
            let many = Elab.non_erased env' fids in
            let shown = List.mapi (fun i x -> Printf.sprintf "%s f%d" (show cx env' (Env.type_of env' x)) i) many in
            let text =
              if a.V.tagged then Printf.sprintf "\"(\" ^ %s ^ \")\"" (concat " ^ \" \" ^ " (quote c.cname :: shown))
              else match shown with [] -> "\"_\"" | [ s ] -> s | ss -> Printf.sprintf "\"(\" ^ %s ^ \")\"" (concat " ^ \" \" ^ " ss)
            in
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
                 | Untagged -> (match branches with (c, text) :: _ -> untuple (fields c) "v" text | [] -> "\"?\"")
                 | _ ->
                     Printf.sprintf "match %s v with %s | _ -> \"?\"" (des cx a)
                       (concat " " (List.map (fun (c, text) -> Printf.sprintf "| (%d, [%s]) -> %s" c.V.index (concat "; " (fields c)) text) branches))))
         | Fn _ -> "\"<function ?>\""
         | ValCtor _ -> "\"<constructor \" ^ (Obj.obj v : ctor).cname ^ \">\""
         | _ -> "\"?\"");
      name

let prelude_ctor cx name = var (Program.ctor cx.env name).cid

let driver cx =
  let io = (Program.ctor cx.env "Exit").adt in
  let of_string =
    if !V.use_externs then "Obj.repr ((s, 0, String.length s) : Ffi_core.slice)"
    else
      "let rec nat n = if n = 0 then build ctor_Zero [] else build ctor_Succ [ nat (n - 1) ] in\n\
      \  let char b = build ctor_MkChar [ build ctor_MkU8 [ nat b ] ] in\n\
      \  String.fold_right (fun ch acc -> build ctor_SCons [ char (Char.code ch); acc ]) s (build ctor_SNil [])"
  in
  concat "\n"
    (List.map (fun n -> Printf.sprintf "let ctor_%s = %s" n (prelude_ctor cx n)) [ "Zero"; "Succ"; "MkU8"; "MkChar"; "SNil"; "SCons"; "Some"; "None"; "Ok"; "Fail"; "MkUnit"; "Cons"; "Nil"; "Exit" ])
  ^ Printf.sprintf "\nlet io_names = [| %s |]\n" (concat "; " (List.map (fun c -> quote c.V.cname) io.ctors))
  ^ {|let build (c : Obj.t) args = let c = (Obj.obj c : ctor) in c.con c.ix args
let des (c : Obj.t) v = (Obj.obj c : ctor).des v
let rec nat v = match des ctor_Zero v with _, [ p ] -> 1 + nat p | _ -> 0
let u8 v = match des ctor_MkU8 v with _, [ n ] -> nat n | _ -> assert false
let of_string s = |} ^ of_string ^ {|
let to_string v =
  let buf = Buffer.create 64 in
  let rec go v =
    match des ctor_SNil v with
    | _, [ ch; rest ] -> Buffer.add_char buf (Char.chr (u8 (List.hd (snd (des ctor_MkChar ch))))); go rest
    | _ -> ()
  in
  go v;
  Buffer.contents buf
let read_file path = In_channel.with_open_bin path In_channel.input_all
let write_file path s = Out_channel.with_open_bin path (fun oc -> Out_channel.output_string oc s)
let flush_to oc s = output_string oc s; flush oc
let program_args = let rec go = function [] -> [] | "--" :: rest -> rest | _ :: rest -> go rest in go (Array.to_list Sys.argv)
let run_io v =
  let result f = match f () with x -> build ctor_Ok [ x ] | exception Sys_error m -> build ctor_Fail [ of_string m ] in
  let step k x = (Obj.obj k : Obj.t -> Obj.t) x in
  let rec loop v =
    let i, fields = des ctor_Exit v in
    match (io_names.(i), fields) with
    | "Exit", [ code ] -> u8 code
    | "WriteOut", [ s; next ] -> flush_to stdout (to_string s); loop next
    | "WriteErr", [ s; next ] -> flush_to stderr (to_string s); loop next
    | "ReadLine", [ k ] -> loop (step k (match In_channel.input_line stdin with Some l -> build ctor_Some [ of_string l ] | None -> build ctor_None []))
    | "ReadFile", [ path; k ] -> loop (step k (result (fun () -> of_string (read_file (to_string path)))))
    | "WriteFile", [ path; s; k ] -> loop (step k (result (fun () -> write_file (to_string path) (to_string s); build ctor_MkUnit [])))
    | "GetArgs", [ k ] -> loop (step k (List.fold_right (fun a acc -> build ctor_Cons [ of_string a; acc ]) program_args (build ctor_Nil [])))
    | _ -> assert false
  in
  loop v
let run_main f = flush_to stdout (to_string ((Obj.obj f : Obj.t -> Obj.t) (of_string (In_channel.input_all stdin))))
|}

let item cx = function
  | Env.Let ([ x ], code) -> Printf.sprintf "let %s : Obj.t = %s" (var x) (expr cx code)
  | Env.Let (ids, code) -> Printf.sprintf "let (%s) : %s = Obj.obj %s" (concat ", " (List.map var ids)) (concat " * " (List.map (fun _ -> "Obj.t") ids)) (expr cx code)
  | Env.Fns fns -> "let rec " ^ concat "\nand " (List.map (fn cx) fns)
  | Env.Final (code, ty) ->
      let consume =
        if Program.is_main cx.env ty then "run_main (" else if Program.is_io cx.env ty then "exit (run_io" else "print_endline (" ^ show cx cx.env ty
      in
      let name = match code with V.CVar x -> (match IntMap.find_opt x cx.env.values with Some (V.VFn cl) -> Some cl.fn.fname | _ -> None) | _ -> None in
      match name with
      | Some n when not (Program.is_main cx.env ty || Program.is_io cx.env ty) -> Printf.sprintf "let () = print_endline %s" (quote ("<function " ^ n ^ ">"))
      | _ -> Printf.sprintf "let () = %s %s)" consume (expr cx code)

let emit env items =
  let cx = collect env items in
  let body = concat "\n" (List.map (item cx) items) in
  let shows = List.rev_map (fun (_, name, body) -> Printf.sprintf "%s (v : Obj.t) : string = %s" name !body) !(cx.shows) in
  concat "\n"
    [ "[@@@warning \"-a\"]";
      "module Ffi_core = struct\n" ^ Ffi_core_source.source ^ "\nend";
      "type ctor = { ix : int; cname : string; con : int -> Obj.t list -> Obj.t; des : Obj.t -> int * Obj.t list }";
      "let absurd () = prerr_endline \"runtime error: absurd code reached\"; exit 1";
      types cx;
      driver cx;
      (if shows = [] then "" else "let rec " ^ concat "\nand " shows);
      body;
      "" ]
