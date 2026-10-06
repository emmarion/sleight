; expect: 7
; Extern functions over numerals in the final function's code: with the FFI stripped, the prelude's models run.

(def-lvl T)
(let ((erased nt)) (prove-predates nat-lvl T))

(def-fns T $ (many main : -> (many (Nat) n))
  (nat-add (predates nt) 3 4))

main
; warns: tests/thunk_nat.sl:8:12: warning: unnecessary `(predates _)`; drop it
