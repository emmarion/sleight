; error: is not a strict subterm of
; The inferred (subterm _) goes at the first subterm argument that differs, with no search: here that
; argument grows, and the second one's decrease is not looked at.

(def-lvl K)
(def-fns K $ (many ack : (subterm many (Nat) m) (subterm many (Nat) n) -> (many (Nat) r))
  (match many n _
    ((Zero) m)
    ((Succ n1) (ack (Succ m) n1))))
