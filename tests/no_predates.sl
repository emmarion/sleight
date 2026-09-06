; error: was not in scope when level
; A bare call to a function at a later level: the inferred Predates proof fails, since the callee's level
; was minted after the caller's.

(def-lvl L0)
(def-lvl L1)
(def-fns L1 $ many f : (many (Nat) n) -> (many (Nat) m) n)
(def-fns L0 $ many g : (many (Nat) n) -> (many (Nat) m) (f n))
