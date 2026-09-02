; needs: list
; error: is not a strict subterm

(def-fns _ $ many loop : (subterm many (Nat) n) -> (many (Nat) m)
  (loop (subterm _) n))
