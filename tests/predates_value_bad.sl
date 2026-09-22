; needs: list
; error: does not relate the callee's level
; A Predates proof about the function value itself is not a call-site proof; the proof must be about its level.

(def-lvl L0)
(def-fns L0 $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-lvl L1)
(let ((erased p)) (prove-predates inc L1))
(def-fns L1 $ (many g : (many (Nat) n) -> (many (Nat) m))
  (inc (predates p) n))
