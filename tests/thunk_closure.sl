; needs: list closure compose
; expect: 5
; Closures returned by factories at the top level, applied by the final function's code: inc4 holds inc3,
; which holds inc and inc2, and add-one closes over its factory's argument.

(def-lvl T)
(let ((erased kt)) (prove-predates K T))
(let ((erased lt)) (prove-predates (level-of add-one) T))
(def-fns T $ (many main : -> (many (Nat) n))
  (inc4 (predates kt) (add-one (predates lt) (Zero))))

main
; warns: tests/thunk_closure.sl:10:32: warning: unnecessary `(predates _)`; drop it
; warns: tests/thunk_closure.sl:10:9: warning: unnecessary `(predates _)`; drop it
