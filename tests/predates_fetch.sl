; expect: 3
; The variable of prove-predates may be a fetch form, as its level may.

(def-fns _ $ (many id : (many (Nat) n) -> (many (Nat) m)) n)
(def-lvl T)
(let ((erased p)) (prove-predates (level-of id) T))
(def-fns T $ (many main : -> (many (Nat) n)) (id (predates p) 3))

main
; warns: tests/predates_fetch.sl:7:50: warning: unnecessary `(predates _)`; drop it
