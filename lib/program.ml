(* The driver's reading of a program's final value (DESIGN.md section 16): a function from String to String is run
   over the input and its result written out; anything else is printed. *)
open Term
module V = Value

let prelude env name = Option.get (Env.lookup { env with Env.scope = env.Env.prelude } name)
let ctor env name = match (Env.entry env (prelude env name)).state with Env.Const (V.VCtorFn c) -> c | _ -> assert false

let is_main env ty =
  let string = App (Var (prelude env "String"), []) in
  match Env.canon env ty with
  | Fn (_, [ { mult = Many; sg = Ty a; _ } ], [ { mult = Many; sg = Ty b; _ } ]) -> equal a string && equal b string
  | _ -> false

let of_string env s =
  if !V.use_externs then Ffi.str s
  else
    let c = ctor env in
    let rec nat n = if n = 0 then V.construct (c "Zero") [] else V.construct (c "Succ") [ nat (n - 1) ] in
    let char b = V.construct (c "MkChar") [ V.construct (c "MkU8") [ nat b ] ] in
    String.fold_right (fun ch acc -> V.construct (c "SCons") [ char (Char.code ch); acc ]) s (V.construct (c "SNil") [])

let to_string env v =
  let c = ctor env and buf = Buffer.create 64 in
  let rec nat v = match V.destruct (c "Zero") v with _, [ p ] -> 1 + nat p | _ -> 0 in
  let byte ch = match V.destruct (c "MkU8") (List.hd (snd (V.destruct (c "MkChar") ch))) with _, [ n ] -> nat n | _ -> assert false in
  let rec go v = match V.destruct (c "SNil") v with _, [ ch; rest ] -> Buffer.add_char buf (Char.chr (byte ch)); go rest | _ -> () in
  go v;
  Buffer.contents buf

let consume ~input ~output ~print env ty v =
  if is_main env ty then output (to_string env (List.hd (Eval.apply v [ of_string env (input ()) ]))) else print (V.show v)
