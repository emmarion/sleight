; expect: 1
(def-fns _ $ (many drop : (unique (Nat) _n) ->) (values))
(def-fns _ $ (many f : (unique (Nat) n) -> (many (Nat) r))
  (let () (drop n))
  (share n))
(f (Succ (Zero)))
