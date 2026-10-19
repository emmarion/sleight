(* The source prelude, lib/prelude.sl, elaborated over Prelude.env ahead of every program (section 42), unless
   [prelude] is false. *)
let load ?(prelude = true) () =
  Ffi.reset ();
  Env.reset_literals ();
  Hashtbl.reset Env.numbering;
  Env.trace := [];
  Elab.gensyms := 0;
  Hashtbl.reset Elab.prims;
  let env = if prelude then Elab.run_toplevel ~loading_prelude:true { Prelude.env with externs = true } (Reader.read "lib/prelude.sl" Prelude_source.source) else Prelude.env in
  { env with prelude = env.scope; externs = not prelude }
