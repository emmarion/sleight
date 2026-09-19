; expect: 1
(def-fns _ $ many choose : (many (Nat) tag) (unique (Nat) x) -> (unique (Nat) r)
  (match many tag _ ((Zero) x) ((Succ k) x)))
(let (unique x) (choose (Zero) (Succ (Zero))))
(share x)
