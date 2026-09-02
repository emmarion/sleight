; needs: list
; expect: (Zero)

(let (erased (Matchable enum Nat (many Zero) (many Succ)) m) (matchable-of Nat))
(let (erased m is m2) (matchable-of Nat))
(Zero)
