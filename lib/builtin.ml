(* The source prelude, lib/prelude.sl, elaborated over Prelude.env ahead of every program (section 41). *)
let load () =
  Ffi.reset ();
  Elab.run_toplevel Prelude.env (Reader.parse Prelude_source.source)
