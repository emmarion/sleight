; expect: 1
(def-fns _ $ (many two : (unique (Nat) x) -> (many (Nat) r s at x))
  (let ((many y)) (share x))
  (values y y))
(let ((many a) (many b)) (two (Succ (Zero))))
b
