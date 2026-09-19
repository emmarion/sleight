; expect: 1
(def-adts $ Ghost : -> Type union (erased G : -> (Ghost)))
(def-fns _ $ many once : (erased (Ghost) g) (unique (Nat) x) -> (unique (Nat) r)
  (match erased g _ ((G) x)))
(let (unique x) (once (G) (Succ (Zero))))
(share x)
