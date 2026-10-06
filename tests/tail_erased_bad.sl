; error: `tail` in an erased position
; A tail or delegate mark in an erased position is a hard error: the call there compiles to nothing,
; so there is no call for the mark to be about. Here the position is erased by the let's erased binder.

(def-lvl L)
(def-fns L $ (many f : (subterm many (Nat) n) -> (many (Nat) m))
  (let-match many n (Succ p)
    ((Zero) (Zero)))
  (let ((erased q)) (tail (f p)))
  (Zero))
(f 3)
