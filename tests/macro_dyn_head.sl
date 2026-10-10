; needs: macro_lib
; error: is a macro, expanded only where its head is constant-known
; error: a macro reaches a body through a run-position binding
(def-fns _ $ (many f : (many (Macro) m) -> (many (Nat) n))
  (m 1))
