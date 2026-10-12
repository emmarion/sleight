(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-fns _ (up ((subterm (Nat) n)) (((Nat) m)) (up (Succ n))))
(up (Zero))
