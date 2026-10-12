; DESIGN.md sections 46 and 53: `_` as a def-fns level, and level-of
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(let ((many inc2)) inc)
(def-fns _ $ (many add2 : (many (Nat) n) -> (many (Nat) m))
  (inc (predates (prove-predates (level-of inc2) (level-of add2))) (Succ n)))
(add2 (Zero))
