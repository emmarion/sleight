; error: erased function `f` called in a non-erased position
(def-fns _ $ (many at same : (many (Nat) x) -> (many (Nat) r at x)) x)
(def-fns _ $ (many apply : (erased (Fn (level-of same) (many (Nat) x) -> (many (Nat) r at x)) f)
    (erased (AtFn (Fn (level-of same) (many (Nat) x) -> (many (Nat) r at x)) f) p) (many (Nat) n) -> (many (Nat) r at n))
  (open-at-fn p)
  (f n))
(apply same (at-fn-of same) 7)
