; needs: list
; error: was not in scope when level

(def-lvl L1)
(def-fns L1 $ (many f : (many (Nat) n) -> (many (Nat) m)) n)
(let ((erased p)) (prove-predates f L1))
