; error: return does not satisfy `at` `(slot-of x)`
(def-fns _ $ (many two : (unique (Nat) x) (unique (Nat) y) -> (unique (Nat) r s at x))
  (values y x))
(let ((unique a) (unique b)) (two (Succ (Zero)) (Zero)))
(share a)
