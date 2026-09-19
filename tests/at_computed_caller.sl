; expect: 1
(def-fns _ $ many move : (unique (Nat) x) -> (unique (Nat) r at x) x)
(let (unique n) (move (Succ (Zero))))
(def-unique _ $ unique inner : -> (unique (Nat) r at n) n)
(let (unique r) (inner))
(share r)
