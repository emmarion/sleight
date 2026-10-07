; needs: list
; error: drop the decrease annotation
; The top level calls without proofs (section 20), so a decrease annotation there is an error.

(def-lvl L)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(inc (predates _) (Zero))
