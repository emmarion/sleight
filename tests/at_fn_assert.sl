; expect: 5
; `(at erased (f ...))` asserts that a call is skipped (section 39), by the proof `def-fns` opened for `f`.
(def-fns _ $ (many at same : (many (Nat) x) -> (many (Nat) r at x)) x)
(let ((many n)) 5)
(at erased (same n))
