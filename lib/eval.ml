open Value

exception Runtime of string

let bind ids vs env =
  if List.length ids <> List.length vs then raise (Runtime "arity mismatch");
  List.fold_left2 (fun env x v -> IntMap.add x v env) env ids vs

(* Adds mutually recursive closures over [env] to it. *)
let close env fns =
  let rec env' =
    lazy (List.fold_left (fun e (x, (fname, params, body)) -> IntMap.add x (VFn { fname; params; body; env = env' }) e) env fns)
  in
  Lazy.force env'

let rec eval env code =
  match code with
  | CVar x -> (match IntMap.find_opt x env with Some v -> [ v ] | None -> raise (Runtime ("unbound at runtime: " ^ string_of_int x)))
  | CConst v -> [ v ]
  | CErased -> [ VToken ]
  | CValues cs -> List.map (eval1 env) cs
  | CApp (f, args, _) -> apply (eval1 env f) (List.map (eval1 env) args)
  | CLet (ids, rhs, body) -> eval (bind ids (eval env rhs) env) body
  | CLetRec (fns, body) -> eval (close env fns) body
  | CMatch (scrut, tagged, branches) -> (
      let v = eval1 env scrut in
      match (tagged, branches, v) with
      | false, [ (_, ids, body) ], v -> eval (bind ids (untuple (List.length ids) v) env) body
      | true, _, VCtor (c, fields) -> (
          let ctor code = match eval1 env code with VCtorFn c -> c.cid | v -> raise (Runtime ("not a constructor: " ^ show v)) in
          match List.find_opt (fun (c', _, _) -> ctor c' = c.cid) branches with
          | Some (_, ids, body) -> eval (bind ids fields env) body
          | None -> raise (Runtime ("no branch for " ^ show v)))
      | _ -> raise (Runtime ("cannot match " ^ show v)))
  | CAbsurd -> raise (Runtime "absurd code reached")

and eval1 env code = match eval env code with [ v ] -> v | vs -> raise (Runtime (Printf.sprintf "expected one value, got %d" (List.length vs)))

and apply f args =
  match f with
  | VFn cl -> eval (bind cl.params args (Lazy.force cl.env)) cl.body
  | VCtorFn c -> [ (if c.tagged then VCtor (c, args) else tuple args) ]
  | v -> raise (Runtime ("cannot apply " ^ show v))
