; error: hint: a call to a strictly lower level needs no decreasing argument; consider defining `helper` at a lower level, or `loop` at a higher one
; A bare same-level call to another function of the block that decreases nothing is refused, with a hint to put the callee below the caller.

(def-lvl X)
(def-fns X
  ((many helper : (many (Nat) n) -> (many (Nat) m))
    (Succ n))
  ((many loop : (subterm many (Nat) n) -> (many (Nat) m))
    (helper n)))
