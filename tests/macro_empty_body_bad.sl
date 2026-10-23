; needs: ../std/macro
(def-macro (unused-empty _args) (Nil _))
(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) r)) (unused-empty))
; error: tests/macro_empty_body_bad.sl:3:14: error: a body needs a final expression
