open Value

exception Runtime of string
let fuel : int option ref = ref None
let perform : (value -> value) ref = ref (fun _ -> raise (Runtime "no world"))
let prim : (Special.t -> value list -> value list) ref = ref (fun p _ -> raise (Runtime ("`" ^ Special.name p ^ "` reached with no macro world")))

let bind ids vs env =
  if List.length ids <> List.length vs then raise (Runtime "arity mismatch");
  List.fold_left2 (fun env x v -> IntMap.add x v env) env ids vs

(* Adds mutually recursive closures over [env] to it. *)
let close env fns =
  let rec env' = lazy (List.fold_left (fun e (x, fn) -> IntMap.add x (VFn { fn; env = env' }) e) env fns) in
  Lazy.force env'

let rec eval env code =
  match code with
  | CVar x when x < 0 -> [ Hashtbl.find literal_values x ]
  | CVar x -> (match IntMap.find_opt (resolve x) env with Some v -> [ v ] | None -> raise (Runtime ("unbound at runtime: " ^ string_of_int x)))
  | CConst v -> [ v ]
  | CErased -> [ VToken ]
  | CValues cs -> List.map (eval1 env) cs
  | CApp (f, args, _) -> apply (eval1 env f) (List.map (eval1 env) args)
  | CLet (ids, rhs, body) -> eval (bind ids (eval env rhs) env) body
  | CLetRec (fns, body) -> eval (close env fns) body
  | CMatch { scrut; shape; branches; default; _ } -> (
      let v = eval1 env scrut in
      let read =
        match shape with
        | Known adt -> dispatch adt.ext adt v
        | Held (code, held) -> (
            match eval1 env code with VMatchable a -> dispatch a.ext held v | x -> raise (Runtime ("not a Matchable: " ^ show x)))
      in
      let enter (_, ids, body) fields = eval (bind ids fields env) body in
      match (read, branches, default) with
      | Some (i, fields), _, _ -> (
          match (List.find_opt (fun (j, _, _) -> j = i) branches, default) with
          | Some branch, _ -> enter branch fields
          | None, Some d -> eval env d
          | None, None -> raise (Runtime ("no branch for " ^ show v)))
      | None, [ ((_, ids, _) as branch) ], _ -> enter branch (let a = match shape with Known a | Held (_, a) -> a in if a.newtype then untuple (List.length ids) v else fields v)
      | None, [], Some d -> eval env d
      | None, _, _ -> raise (Runtime ("no discriminant to tell the branches of " ^ show v ^ " apart")))
  | CCellAlloc (c, []) -> [ construct c [] ]
  | CCellAlloc (c, ss) -> [ VCtor (c, Array.of_list (List.map (eval1 env) ss)) ]
  | CCellWrite (_, c, ss) | CCellCopy (_, c, ss) -> (
      match eval1 env c with
      | VWord _ as v -> [ v ]
      | VCtor (k, fs) as v ->
          let copies = match code with CCellCopy _ -> true | _ -> false in
          let fs = if copies then Array.copy fs else fs in
          List.iter (fun (i,s) -> fs.(i) <- eval1 env s) ss;
          [ (if copies then VCtor (k, fs) else v) ]
      | _ -> raise (Runtime "not a cell"))
  | CCellRead (_, i, c) -> (match eval1 env c with VCtor (_, fs) -> [ fs.(i) ] | _ -> raise (Runtime "not a cell"))
  | CWorldDo c -> [ !perform (eval1 env c) ]
  | CPrim (p, cs) -> (
      match p, List.map (eval1 env) cs with
      | Special.SettledValue, [ VHandle (_, _, _, v) ] -> [ v ]
      | Special.SlotEq, [ a; b; none; some ] -> [ (if a == b then some else none) ]
      | Special.SettledMult, [ h; e; m; u ] -> [ (match h with VHandle (_, _, Erased, _) -> e | VHandle (_, _, Unique, _) -> u | _ -> m) ]
      | Special.SettledErase, [ VHandle (x, r, _, _) ] -> [ VHandle (x, r, Erased, VToken) ]
      | Special.SettledType, [ VHandle (x, r, _, _) ] -> [ (match r with MintedIs -> VHandle (x, MintedType, Erased, VToken) | MintedType -> VHandle (!Term.type_entry, MintedIs, Erased, VToken)) ]
      | p, vs -> !prim p vs)
  | CAbsurd -> raise (Runtime "absurd code reached")

and eval1 env code = match eval env code with [ v ] -> v | vs -> raise (Runtime (Printf.sprintf "expected one value, got %d" (List.length vs)))

and apply f args =
  let spend k run =
    match !fuel with
    | None -> run ()
    | Some n when n < k -> raise (Runtime "out of fuel")
    | Some n -> fuel := Some (n - k); Fun.protect ~finally:(fun () -> fuel := Some n) run
  in
  match f with
  | VFn { fn = { impl = Some impl; _ }; _ } when !use_externs -> spend 1 (fun () -> impl args)
  | VFn cl -> spend 2 (fun () -> eval (bind cl.fn.params args (Lazy.force cl.env)) cl.fn.body)
  | VCtorFn c -> spend 1 (fun () -> [ construct c args ])
  | v -> raise (Runtime ("cannot apply " ^ show v))
