; expect: 8
; As at_argument_literal.sl, inside a body.
(def-lvl K)
(def-fns _ $ (many mk : (many (Nat) x) -> (many (Fn K (many (Nat) y) -> (many (Nat) r at x)) g))
  (def-fns K $ (many f : (many (Nat) _y) -> (many (Nat) r at x)) x)
  f)
(def-fns _ $ (many use : (many (Nat) n) -> (many (Nat) r))
  (let ((many g)) (mk 4))
  (let ((many a)) (g n))
  (nat-add a $ g 0))
(use 5)
