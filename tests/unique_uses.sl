; expect: 2
(def-fns _ $ (many move : (unique (Nat) n) -> (unique (Nat) r)) n)
(let ((unique x)) (Succ (Zero)))
(let ((unique y)) (move x))
(let ((erased p)) (Refl (Nat) x))
(let ((many a)) (share y))
(let ((many b)) (share y))
(nat-add a b)
