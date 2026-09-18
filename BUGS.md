# Bugs

Defects found in the implementation, for the owner to get to. Written by
Claude sessions; each entry says how it was reproduced, and nothing here
is a design decision. Remove an entry when it is fixed.

1. **An unsolvable `_` in a constructor's return type crashes the
   reference and passes `slc`.** Found while probing SUGAR.md 6.

   ```scheme
   (def-adts (V : ((Nat) n) -> Type
     enum
     (many VS : (erased (Nat) k) (erased (V k) v) -> (V (Succ _)))))
   ```

   `dune exec bin/main.exe file.sl` dies with `Fatal error: exception
   Not_found`; with `OCAMLRUNPARAM=b` the backtrace is `Env.fact`, reached
   from `Env.canon` through `Term.map_vars`, so on this session's reading
   the return type's meta is canonicalized after its scope is gone.
   `_build/self/slc -- lib/prelude.sl file.sl` accepts the file with
   exit code 0, leaving an unsolved hole in a type. Every other fact goes
   through `Elab.settle` (ASSUMPTIONS 117); a constructor's return type
   in `elab_valctor` (`lib/elab.ml`, near line 372) and its analogue in
   `self/elab.sl` do not. A solvable `_` there is fine and useful:
   `(P _ (Nil (Nat)))` and `(P (Nat) (Nil _))` are solved against the
   type constructor's telescope by both compilers. Suggested fix: settle
   the return type in both, and add a `tests/wild_adt_bad.sl` expecting
   `cannot infer the _`.
