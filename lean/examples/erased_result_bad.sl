(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-lvl L)
(def-fns L (f ((erased (Nat) n)) (((Nat) y)) n))
(f (Zero))
