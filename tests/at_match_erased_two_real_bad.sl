; error: only one real branch

(def-fns _ $ (many same : (erased (Bool) b) (many (Nat) n) -> (many (Nat) r at n))
  (match erased b (at (((Nat) r at n)))
    ((BTrue) n)
    ((BFalse) n)))

(same (BTrue) 3)
