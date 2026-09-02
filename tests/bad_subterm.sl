; needs: list
; error: is not a strict subterm

(def-lvl X)
(def-fns X $ many loop : (subterm many (Nat) n) -> (many (Nat) m)
  (let (erased p) (prove-subterm n n))
  (loop (subterm p) n))
