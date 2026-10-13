; two real branches need a discriminant an erased scrutinee does not have
(def-fns _ $ (many pick : (erased (Nat) n) -> (many (Nat) m))
  (match erased n (((Nat) r))
    ((Zero) 0)
    ((Succ k) 7)))
(pick 2)
