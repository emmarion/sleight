; needs: ../std/macro
(def-macro (m _args) (qq (Succ (Zero))))
(def-fns _ $ (many f : -> (many (Nat) r)) (let ((many y) (m))) (Zero))
; error: tests/macro_tele_entry_bad.sl:2:26: error: malformed telescope entry `(Succ (Zero))`
