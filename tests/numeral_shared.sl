; expect: 3
; Every occurrence of a numeral is one entry, so the literal's proof serves an alias of it,
; and a numeral inside a body is an embedded Const.

(def-fns _ $ (erased five : (erased (Nat) n) (erased (Numeral (B1 (B2 (BZ))) n) v) -> (erased (Nat) m))
  n)

(def-fns _ $ (many add-two : (many (Nat) n) -> (many (Nat) m))
  (nat-add (predates _) n 2))

(let ((many x)) 5)
(let ((many y)) 5)
(let ((erased r)) (five x (numeral-of 5)))
(add-two 1)
; warns: tests/numeral_shared.sl:9:12: warning: unnecessary `(predates _)`; drop it
