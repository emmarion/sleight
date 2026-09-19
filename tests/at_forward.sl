; expect: 2
(def-fns _ $ many move : (unique (Nat) x) -> (unique (Nat) r at x) x)
(def-fns _ $ many twice : (unique (Nat) x) -> (unique (Nat) r at x)
  (let (unique y) (move x))
  (tail (move y)))
(let (unique y) (twice (Succ (Succ (Zero)))))
(share y)
