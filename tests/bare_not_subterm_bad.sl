; error: is not a strict subterm of
; A bare same-level call whose subterm argument differs but does not decrease is refused by the proof, not
; for lacking an annotation.

(def-lvl X)
(def-fns X $ many loop : (subterm many (Nat) n) -> (many (Nat) m)
  (loop (Succ n)))
