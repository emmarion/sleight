(* The source prelude, lib/prelude.sl, elaborated over Prelude.env ahead of every program (section 41), unless
   [prelude] is false. *)
let load ?(prelude = true) () =
  Ffi.reset ();
  Hashtbl.reset Env.numbering;
  Env.trace := [];
  let env = if prelude then Elab.run_toplevel Prelude.env (Reader.parse "lib/prelude.sl" Prelude_source.source) else Prelude.env in
  { env with prelude = env.scope }
