; expect: 5
; `(at (f ...))` asserts that a call is skipped (AT_REDESIGN A10), by the proof `def-fns` opened for `f`.
(def-fns _ $ (many at same : (many (Nat) x) -> (many (Nat) r at x)) x)
(let ((many n)) 5)
(at (same n))
