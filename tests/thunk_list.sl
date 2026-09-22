; needs: list
; expect: 2
; A final function from no arguments: the driver applies it and prints the result, so the value is computed by
; code (at runtime once extracted) over the embedded constant list-xs.

(def-lvl T)
(let ((erased lt)) (prove-predates list-lvl T))
(def-fns T $ (many main : -> (many (Nat) n))
  (length (predates lt) (Nat) list-xs))

main
