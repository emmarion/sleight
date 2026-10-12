(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-adts (Bool () (True () (Bool)) (False () (Bool))))
(let (((Bool) a)) (Zero))
a
