; needs: ../std/macro
(def-macro (bad-tmpl _args)
  (qq (Succ (BTrue))))
(bad-tmpl)
; error: tests/macro_qq_ctor_name_bad.sl:3:13: error: argument 1, `pred`, of `Succ`: type mismatch: expected `(Nat)`, got `(Bool)`
; error: lib/prelude.sl:13:3: note: value constructor `Succ` is declared here
