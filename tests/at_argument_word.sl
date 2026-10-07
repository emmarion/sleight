; expect: 6
; The argument `(Succ n)` is bound to a temporary before the call (section 15); the closure's `at` names
; that temporary's slot, and `(g 3)` reads its word after the `let` has closed.
(def-lvl K)
(def-fns _ $ (many mk : (many (Nat) x) -> (many (Fn K (many (Nat) y) -> (many (Nat) r at x)) g))
  (def-fns K $ (many f : (many (Nat) y) -> (many (Nat) r at x)) x)
  f)
(let ((many n)) 5)
(let ((many g)) (mk (Succ n)))
(g 3)
