(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(let (((Succ (Zero)) is a)) (Zero))
a
