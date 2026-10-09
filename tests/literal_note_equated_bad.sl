; error: this `match` is missing a branch for the following unrefuted constructor:
; error: note: value constructor `Refl`, which is declared here
; error: 3 in `(Eq (Nat) 3 5)` is a numeral literal, opaque to the checker by default; `unary`, `prove-literal-lt` or `numeral-of` can expose more
; error: 5 in `(Eq (Nat) 3 5)` is a numeral literal, opaque to the checker by default; `unary`, `prove-literal-lt` or `numeral-of` can expose more
; Two literals equated by a branch are not told apart until a refutation through (prove-literal-lt 3 5) is written; the note
; names both, the one forcing bound and the one it was bound to.

(def-lvl L)
(def-fns L $ (many h : (erased (Eq (Nat) 3 5) e) -> (many (False) f))
  (match erased e _))
(Zero)
