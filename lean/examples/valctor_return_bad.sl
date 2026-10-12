; ASSUMPTIONS.md 80: a ValCtor's return is not headed by one of its own fields
(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-lvl L)
(def-fns L (f (((ValCtor (((TyCtor ()) T)) (T)) c)) (((Nat) n)) (Zero)))
(Zero)
