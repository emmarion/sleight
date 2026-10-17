; error: type mismatch
; numeral-of yields the proof for the literal's own spelling, so 6's cannot stand in for 5's.

(def-fns _ $ (erased f : (erased (Nat) n) (erased (Numeral (B1 (B2 (BZ))) n) _v) -> (erased (Nat) m))
  n)

(let ((erased r)) (f 6 (numeral-of 6)))
(Zero)
