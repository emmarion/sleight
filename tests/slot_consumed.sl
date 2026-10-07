; expect: 1
(def-fns _ $ (many move : (unique (Nat) x) -> (unique (Nat) r at x)) x)
(let ((unique x)) (Succ (Zero)))
(let ((unique y)) (move x))
(let ((many s)) (slot-of x))
(let ((erased (Eq (Slot) s (slot-of y)) same)) (Refl (Slot) s))
(share y)
