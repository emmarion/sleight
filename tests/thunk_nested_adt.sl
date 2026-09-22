; needs: list nested_adt
; expect: 2
; A nested def-adts built and matched by the final function's code.

(def-lvl T)
(let ((erased xt)) (prove-predates X T))
(def-fns T $ (many main : -> (many (Nat) n))
  (twice (predates xt) (Succ (Zero))))

main
