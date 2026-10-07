; error: argument 2, `y`, of `f` does not satisfy `at` `(slot-of a)`
; A parameter's `at` claim is checked in an erased position too (AT_REDESIGN A5).
(def-fns _ $ (many f : (many (Nat) x) (many (Nat) y at x) -> (many (Nat) r)) x)
(def-fns _ $ (many g : (many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (let ((erased r)) (f a b))
  a)
