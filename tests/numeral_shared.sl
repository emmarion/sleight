; expect: (Succ (Succ (Succ (Zero))))
; Every occurrence of a numeral is one entry, so a proof fetched through one alias serves another,
; and a numeral inside a body is an embedded Const.

(def-fns _ $ erased five : (erased (Nat) n) (erased (Numeral (B1 (B2 (BZ))) n) v) -> (erased (Nat) m)
  n)

(def-fns _ $ many add-two : (many (Nat) n) -> (many (Nat) m)
  (nat-add (predates _) n 2))

(let (many x) 5)
(let (many y) 5)
(let (erased r) (five x (numeral-of y)))
(add-two 1)
