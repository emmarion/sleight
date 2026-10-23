; needs: ../std/macro
(def-macro (m _args) (qq Zero))
(def-fns _ $ (many f : -> (many (Nat) r)) (let ((many y) (m))) (Zero))
; error: tests/macro_tele_atom_bad.sl:2:26: error: expected a telescope entry, got `Zero`
