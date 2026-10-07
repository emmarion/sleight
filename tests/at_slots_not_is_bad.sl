; error: value mismatch
(def-fns _ $ (many outer : (many (Nat) x) (many (Nat) y) -> (many (Nat) r))
  (def-fns _ $ (many inner :
      (erased (Eq (Slot) (slot-of x) (slot-of y)) same) -> (many x is r at x))
    (let-match erased same (Refl _ _)) y)
  x)
