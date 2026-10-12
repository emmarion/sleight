(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-adts (Two (((Nat) a))
  (MkTwo (((Nat) a) ((Succ (Succ a)) is s)) (Two a))))
(MkTwo (Zero) (Succ (Zero)))
