; error: `at` in an erased position
(def-fns _ $ (many at f : (many (Nat) p) -> (many (Nat) r at p)) p)
(def-fns _ $ (many g : (many (Nat) x) -> (many (Nat) r))
  (let ((erased r)) (at erased (f x)))
  x)
