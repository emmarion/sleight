; needs: list
; expect: 1
; A function type built by Fn and named by a let, then used as a parameter type.

(def-lvl L)
(let (erased T) (Fn L (many (Nat) n) -> (many (Nat) m)))
(def-fns L $ many inc : (many (Nat) n) -> (many (Nat) m) (Succ n))
(def-lvl K)
(let (erased p) (prove-predates L K))
(def-fns K $ many apply : (many T f) (many (Nat) x) -> (many (Nat) y)
  (f (predates p) x))
(apply inc (Zero))
