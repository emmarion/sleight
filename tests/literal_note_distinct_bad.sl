; error: constructor `Refl` has 0 branches
; error: 3 in `(Eq (Nat) 3 5)` is a numeral literal, opaque to the checker; consider `unary`, `distinct` or `numeral-of`
; error: 5 in `(Eq (Nat) 3 5)` is a numeral literal, opaque to the checker; consider `unary`, `distinct` or `numeral-of`
; Two literals equated by a branch are not told apart until (distinct 3 5) refutes the branch; the note
; names both, the one forcing bound and the one it was bound to.

(def-lvl L)
(def-fns L $ (many h : (erased (Eq (Nat) 3 5) e) -> (many (False) f))
  (match erased e _))
(Zero)
