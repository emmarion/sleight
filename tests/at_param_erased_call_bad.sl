; error: argument 2, `y`, of `f` does not satisfy `at` `(slot-of a)`
; A parameter's `at` claim is checked in an erased position too (section 36).
(def-fns _ $ (many f : (many (Nat) x) (many (Nat) y at x) -> (many (Nat) r)) x)
(def-fns _ $ (many g : (many (Nat) a) (many (Nat) b) -> (many (Nat) r))
  (let ((erased r)) (f a b))
  a)
; warns: tests/at_param_erased_call_bad.sl:3:39: warning: unused `y`; rename it `_y`
