; error: `f` is not an at-function here: no `AtFn` proof for it is open
(def-fns _ $ (many at same : (many (Nat) x) -> (many (Nat) r at x)) x)
(def-fns _ $ (many apply : (erased (Fn (level-of same) (many (Nat) x) -> (many (Nat) r at x)) f)
    (many (Nat) n) -> (many (Nat) r at n))
  (at erased (f n)))
(apply same 7)
