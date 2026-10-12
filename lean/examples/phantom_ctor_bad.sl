(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-adts (Opt () (None () (Opt)) (erased Hidden (((Nat) n)) (Opt))))
(let ((many f)) Hidden)
(f (Zero))
