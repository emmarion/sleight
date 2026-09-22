; needs: list map
; error: delegate

(def-lvl V)
(let ((erased piv)) (prove-predates I V))
(def-fns V $ (many inc-twice : (many (Nat) n) -> (many (Nat) m))
  (delegate (inc (predates piv) (Succ n))))
