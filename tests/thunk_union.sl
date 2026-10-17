; needs: list union special_value
; expect: (%match)
; An untagged union matched, and a Special built, by the final function's code.

(def-lvl T)
(let ((erased xt)) (prove-predates X T))
(let ((erased UX)) (level-of get-left))
(let ((erased uxt)) (prove-predates UX T))
(def-fns T $ (many main : -> (many (Special) s))
  (match many (get-left (predates uxt) (L (Succ (Zero)))) (((Special) r))
    ((Zero) let)
    ((Succ _) (pick (predates xt) (BFalse)))))

main
; warns: tests/thunk_union.sl:10:25: warning: unnecessary `(predates _)`; drop it
; warns: tests/thunk_union.sl:12:21: warning: unnecessary `(predates _)`; drop it
