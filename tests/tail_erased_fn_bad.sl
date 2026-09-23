; error: `tail` in an erased position
; The body of an erased function is an erased position throughout (section 20), so a tail mark there
; is refused as in any other erased position.

(def-lvl L)
(def-fns L $ (erased f : (subterm many (Nat) n) -> (many (Nat) m))
  (match erased n _
    ((Zero) (Zero))
    ((Succ p) (tail (f p)))))
(Zero)
