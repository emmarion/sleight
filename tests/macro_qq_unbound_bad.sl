; needs: ../std/macro
(def-macro (wrap _args)
  (qq (Cons (Nat) nowhere $ Nil (Nat))))
(wrap)
; error: tests/macro_qq_unbound_bad.sl:3:19: error: an unbound name in a `qq` template
