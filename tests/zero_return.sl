; needs: list
; expect: (Zero)
; A function returning no values, and a let binding none (sections 11, 16).

(def-lvl X)
(def-fns X $ many nothing : (many (Nat) n) -> (values))
(let (nothing (Zero)))
(def-lvl Y)
(let (erased p) (prove-predates X Y))
(def-fns Y $ many use : (many (Nat) n) -> (many (Nat) m)
  (let (nothing (predates p) n))
  n)
(use (Zero))
