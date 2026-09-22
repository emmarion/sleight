; error: decreases no subterm argument
; A bare same-level call passing its subterm argument unchanged: no position differs, so no proof is inferred.

(def-lvl X)
(def-fns X $ (many loop : (subterm many (Nat) n) -> (many (Nat) m))
  (loop n))
