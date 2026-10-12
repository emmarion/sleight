(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-fns _ (absurd lie (((Nat) n)) (((Nat) m)) n))
(lie (Zero))
