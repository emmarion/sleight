; needs: list closure compose
; expect: (Succ (Succ (Succ (Succ (Succ (Zero))))))
; Closures returned by factories at the top level, applied by the final function's code: inc4 holds inc3,
; which holds inc and inc2, and add-one closes over its factory's argument.

(def-lvl T)
(let (erased kt) (prove-predates K T))
(let (erased AL) (level-of add-one))
(let (erased lt) (prove-predates AL T))
(def-fns T $ many main : -> (many (Nat) n)
  (inc4 (predates kt) (add-one (predates lt) (Zero))))

main
