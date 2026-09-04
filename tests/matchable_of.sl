; needs: list
; expect: (Zero)

(let (erased (Matchable enum Nat (many Zero) (many Succ)) m) (matchable-of Nat))
(let (erased m is m2) (matchable-of Nat))
; A renamed type constructor is read through its alias, as a renamed value constructor already was
; (ASSUMPTIONS 78, tests/ctor_alias.sl).
(let (erased N) Nat)
(let (erased (Matchable enum Nat (many Zero) (many Succ)) m3) (matchable-of N))
(Zero)
