open Value

exception Runtime of string

let construct c args =
  let info = Hashtbl.find ctors c in
  match info.repr with Tagged -> VCtor (c, args) | Field i -> List.nth args i | Unspecified -> VToken

let bind ids vs env =
  if List.length ids <> List.length vs then raise (Runtime "arity mismatch");
  List.fold_left2 (fun env x v -> IntMap.add x v env) env ids vs

let rec eval env code =
  match code with
  | CVar x -> (
      match IntMap.find_opt x env with
      | Some v -> [ v ]
      | None -> (match Hashtbl.find_opt consts x with Some v -> [ v ] | None -> raise (Runtime ("unbound at runtime: " ^ string_of_int x))))
  | CErased -> [ VToken ]
  | CValues cs -> List.map (eval1 env) cs
  | CApp (f, args, _) -> apply (eval1 env f) (List.map (eval1 env) args)
  | CLet (ids, rhs, body) -> eval (bind ids (eval env rhs) env) body
  | CLetRec (fns, body) ->
      let rec env' =
        lazy
          (List.fold_left
             (fun e (x, (fname, params, body)) -> IntMap.add x (VFn { fname; params; body; env = env' }) e)
             env fns)
      in
      eval (Lazy.force env') body
  | CMatch (scrut, branches) -> (
      match eval1 env scrut with
      | VCtor (c, fields) -> (
          match List.find_opt (fun (c', _, _) -> c = c') branches with
          | Some (_, ids, body) -> eval (bind ids fields env) body
          | None -> raise (Runtime ("no branch for " ^ show (VCtor (c, fields)))))
      | v -> raise (Runtime ("match on non-constructor value " ^ show v)))
  | CAbsurd -> raise (Runtime "absurd code reached")

and eval1 env code = match eval env code with [ v ] -> v | vs -> raise (Runtime (Printf.sprintf "expected one value, got %d" (List.length vs)))

and apply f args =
  match f with
  | VFn cl -> eval (bind cl.params args (Lazy.force cl.env)) cl.body
  | VCtorFn c -> [ construct c args ]
  | v -> raise (Runtime ("cannot apply " ^ show v))
