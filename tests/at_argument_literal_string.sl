; expect: "ab"
; As at_argument_literal.sl, for a string literal and a character literal.
(def-lvl K)
(def-fns _ $ (many mk : (erased Type A) (many A x) -> (many (Fn K (many (Nat) y) -> (many A r at x)) g))
  (def-fns K $ (many f : (many (Nat) _y) -> (many A r at x)) x)
  f)
(let ((many g)) (mk _ "ab"))
(let ((many h)) (mk _ #\c))
(let ((many c)) (h 0))
(g 0)
