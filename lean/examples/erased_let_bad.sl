(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(let ((erased x)) (Zero))
(let ((many y)) x)
y
