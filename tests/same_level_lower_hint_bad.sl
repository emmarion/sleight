; error: hint: a call to a strictly lower level needs no decreasing argument; consider defining `helper` at a lower level
; A bare same-level call to another function of the block that decreases nothing is refused, with a hint to lower the callee's level.

(def-lvl X)
(def-fns X
  ((many helper : (many (Nat) n) -> (many (Nat) m))
    (Succ n))
  ((many loop : (subterm many (Nat) n) -> (many (Nat) m))
    (helper n)))
