; needs: list
; error: needs a (subterm p) annotation

(def-lvl X)
(def-fns X $ many loop : (subterm many (Nat) n) -> (many (Nat) m)
  (loop n))
