open Value

exception Runtime of string

let bind ids vs env =
  if List.length ids <> List.length vs then raise (Runtime "arity mismatch");
  List.fold_left2 (fun env x v -> IntMap.add x v env) env ids vs

(* Adds mutually recursive closures over [env] to it. *)
let close env fns =
  let rec env' = lazy (List.fold_left (fun e (x, fn) -> IntMap.add x (VFn { fn; env = env' }) e) env fns) in
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
  | CMatch { scrut; shape; branches; default } -> (
      let v = eval1 env scrut in
      let read =
        match shape with
        | Known adt -> dispatch adt.ext adt.tagged v
        | Held (code, tags) -> (
            match eval1 env code with VMatchable a -> dispatch a.ext tags v | x -> raise (Runtime ("not a Matchable: " ^ show x)))
      in
      let enter (_, ids, body) fields = eval (bind ids fields env) body in
      match (read, branches, default) with
      | Some (i, fields), _, _ -> (
          match (List.find_opt (fun (j, _, _) -> j = i) branches, default) with
          | Some branch, _ -> enter branch fields
          | None, Some (is, d) when List.mem i is -> eval env d
          | None, _ -> raise (Runtime ("no branch for " ^ show v)))
      | None, [ ((_, ids, _) as branch) ], _ -> enter branch (untuple (List.length ids) v)
      | None, [], Some (_, d) -> eval env d
      | None, _, _ -> raise (Runtime ("no discriminant to tell the branches of " ^ show v ^ " apart")))
  | CAbsurd -> raise (Runtime "absurd code reached")

and eval1 env code = match eval env code with [ v ] -> v | vs -> raise (Runtime (Printf.sprintf "expected one value, got %d" (List.length vs)))

and apply f args =
  match f with
  | VFn { fn = { impl = Some impl; _ }; _ } when !use_externs -> impl args
  | VFn cl -> eval (bind cl.fn.params args (Lazy.force cl.env)) cl.fn.body
  | VCtorFn c -> [ construct c args ]
  | v -> raise (Runtime ("cannot apply " ^ show v))
