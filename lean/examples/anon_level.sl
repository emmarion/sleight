; DESIGN.md sections 46 and 53: `_` as a def-fns level, and level-of
(def-adts (Nat () (Zero () (Nat)) (Succ (((Nat) pred)) (Nat))))
(def-fns _ (inc (((Nat) n)) (((Nat) m)) (Succ n)))
(let (inc2) inc)
(def-fns _ (add2 (((Nat) n)) (((Nat) m))
  (inc (predates (prove-predates (level-of inc2) (level-of add2))) (Succ n))))
(add2 (Zero))
