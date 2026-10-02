; needs: list
; error: cannot infer `_?1` in `(List _?1)`
; With nothing expected of the match, a `_` in its annotation has nothing to be solved by.
(let ((many xs))
  (match many (Zero) (((List _) r))
    ((Zero) (Nil (Nat)))
    ((Succ k) (Nil (Nat)))))
xs
