; expect: 1
; `slot-of` may name a telescope binder (AT_REDESIGN A6): a proof that two parameters share a word lets a
; return promised at one be the other.
(def-fns _ $ (many pick : (many (Nat) x) (many (Nat) y) (erased (Eq (Slot) (slot-of x) (slot-of y)) same) -> (many (Nat) r at x))
  (let-match erased same (Refl _ _))
  y)
(let ((many n)) 1)
(pick n n (Refl _ _))
