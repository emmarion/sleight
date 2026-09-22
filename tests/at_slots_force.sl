; expect: 1
(def-fns _ $ (many outer : (many (Nat) x) (many (Nat) y) -> (many (Nat) r))
  (def-fns _ $ (many inner :
      (erased (Eq (Slot) (SlotHolds x) (SlotHolds y)) same) -> (many (Nat) r at x))
    (let-match erased same (Refl _ _)) y)
  x)
(outer (Succ (Zero)) (Zero))
