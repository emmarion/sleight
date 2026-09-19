; expect: 1
(def-fns _ $ many move : (unique (Nat) x) -> (unique (Nat) r at x) x)
(let (unique x) (Succ (Zero)))
(let (unique y) (move x))
(let (many s) (SlotHolds x))
(let (erased (Eq (Slot) s (SlotHolds y)) same) (Refl (Slot) s))
(share y)
