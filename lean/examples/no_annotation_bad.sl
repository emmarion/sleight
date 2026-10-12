(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-lvl L)
(def-fns L (loop (((Nat) n)) (((Nat) m)) (loop n)))
(loop (Zero))
