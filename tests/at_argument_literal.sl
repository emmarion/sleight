; expect: 1
; As at_argument_word.sl, the argument a literal: the closure's `at` names the literal's own entry, which is
; outside the scope (section 45), and `(g 0)` reads its word from there.
(def-lvl K)
(def-fns _ $ (many mk : (many (Nat) x) -> (many (Fn K (many (Nat) y) -> (many (Nat) r at x)) g))
  (def-fns K $ (many f : (many (Nat) _y) -> (many (Nat) r at x)) x)
  f)
(let ((many g)) (mk 1))
(g 0)
