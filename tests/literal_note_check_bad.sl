; error: type mismatch: expected `(Vec 3)`, got `(Vec (Succ 2))`
; error: 3 in `(Vec 3)` is a numeral literal, opaque to the checker; consider `unary`, `distinct` or `numeral-of`
; A literal index meets a Succ shape when a value constructor's return is checked against the telescope it is
; returned into: the unifier sees 3 as an atom, so the check fails, and the note names the literal. (unary 3 2)
; would make 3 (Succ 2).

(def-adts $ (Vec : ((Nat) n) -> Type)
  enum
  (many VNil : -> (Vec (Zero)))
  (many VCons : (erased (Nat) n) (many (Nat) h) (many (Vec n) t) -> (Vec (Succ n))))
(def-fns _ $ (many push : (many (Vec 2) xs) -> (many (Vec 3) ys))
  (VCons _ 7 xs))
(Zero)
