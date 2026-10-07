; expect: 3
; A parameter written `at` an earlier one (section 36): the argument for it must sit in the target's slot,
; and nothing is passed for it (section 36).
(def-fns _ $ (many both : (many (Nat) x) (many (Nat) y at x) -> (many (Nat) r at y))
  y)
(let ((many a)) 3)
(both a a)
