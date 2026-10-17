; needs: list
; expect: 0
; A function returning no values, and a let binding none (sections 26, 27).

(def-lvl X)
(def-fns X $ (many nothing : (many (Nat) _n) ->) (values))
(let () (nothing (Zero)))
(def-lvl Y)
(let ((erased p)) (prove-predates X Y))
(def-fns Y $ (many use : (many (Nat) n) -> (many (Nat) m))
  (let () (nothing (predates p) n))
  n)
(use (Zero))
; warns: tests/zero_return.sl:11:20: warning: unnecessary `(predates _)`; drop it
