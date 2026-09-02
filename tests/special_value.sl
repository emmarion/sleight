; needs: list union
; expect: (%match)
; A special form held as ordinary data, matched on through the Special Matchable.

(def-lvl X)
(def-fns X $ many pick : (many (Bool) b) -> (many (Special) s)
  (match many b (((Special) r))
    ((True) let)
    ((False) match)))

(pick (False))
