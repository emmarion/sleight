; needs: ../std/macro
; error: tests/macro_frame_hoisted_bad.sl:4:30: error: argument 1, `pred`, of
; error: tests/macro_frame_hoisted_bad.sl:6:43: note: in the expansion of `hoisted` here
(let ((many tmpl)) (qq (Succ (BTrue))))
(def-macro (hoisted _args) tmpl)
(def-fns _ $ (many f : -> (many (Nat) n)) (hoisted))
