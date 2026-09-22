; needs: list first_class
; expect: 1
; A first-class match performed by the final function's code.

(def-lvl T)
(let ((erased xt)) (prove-predates X T))
(def-fns T $ (many main : -> (many (Nat) n))
  (open (predates xt) Box MkBox (matchable-of Box) (MkBox (Succ (Zero)))))

main
