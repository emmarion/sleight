; needs: macro_lib
; error: is a macro, expanded only where its head is constant-known
(def-fns _ $ (many f : (many (Macro) m) -> (many (Nat) n))
  (m 1))
