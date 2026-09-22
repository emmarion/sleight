(* The source prelude, lib/prelude.sl, elaborated over Prelude.env ahead of every program (section 41). *)
let load () =
  Ffi.reset ();
  Env.trace := [];
  let env = Elab.run_toplevel Prelude.env (Reader.parse "lib/prelude.sl" Prelude_source.source) in
  { env with prelude = env.scope }
