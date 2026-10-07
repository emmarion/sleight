; needs: list
; expect: 0

(let ((erased (Matchable enum extern Nat (many Zero) (many Succ)) m)) (matchable-of Nat))
(let ((erased m is m2)) (matchable-of Nat))
; A renamed type constructor is read through its alias, as a renamed value constructor already was
; (ASSUMPTIONS 78, tests/ctor_alias.sl).
(let ((erased N)) Nat)
(let ((erased (Matchable enum extern Nat (many Zero) (many Succ)) m3)) (matchable-of N))
; An alias of a type's own Matchable opens as that Matchable: the two merge, and matching on Nat reads the
; def-adts one as before (DESIGN.md section 8).
(open-adt erased m3)
(match many 1 (((Nat) r)) ((Zero) (Succ (Zero))) ((Succ k) k))
