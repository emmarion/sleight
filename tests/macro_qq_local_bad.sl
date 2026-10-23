; needs: ../std/macro
(def-macro (wrap args)
  (qq (Cons (Nat) args $ Nil (Nat))))
(wrap 1)
; error: tests/macro_qq_local_bad.sl:3:19: error: a local name in a `qq` template; write it `(~ x)`
