; error: constructor `Refl` has 0 branches
; error: 3 and 5 are numeral literals, opaque to the checker
; error: `(distinct a b)` refutes a branch that equates two different literals
; Two literals equated by a branch are not told apart until (distinct 3 5) refutes the branch; the note
; names both.

(def-lvl L)
(def-fns L $ (many h : (erased (Eq (Nat) 3 5) e) -> (many (False) f))
  (match erased e _))
(Zero)
