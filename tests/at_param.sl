; expect: 3
; A parameter written `at` an earlier one (AT_REDESIGN A5): the argument for it must sit in the target's slot,
; and nothing is passed for it (A3).
(def-fns _ $ (many both : (many (Nat) x) (many (Nat) y at x) -> (many (Nat) r at y))
  y)
(let ((many a)) 3)
(both a a)
