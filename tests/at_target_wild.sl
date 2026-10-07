; expect: 0
(def-fns _ $ (many f : (erased (Nat) n) (erased n is m at n) -> ) (values))
(def-fns _ $ (many g : (erased (Nat) n) (erased (Nat) m at n) (erased (Eq (Nat) n m) p) -> ) (values))
(let ((erased x)) 3)
(let () (f x x))
(let () (f _ x))
(let () (f _ 3))
(let () (g _ x (Refl _ x)))
0
