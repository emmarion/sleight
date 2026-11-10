; A tainted head is never dispatched as a special form or a macro.
(let ((many m)) (sorry (((Special) s))))
(m ((many x)) 3)
; error: tests/sorry_head_bad.sl:3:2: error: `m` relies on `sorry`, so it is not dispatched as a special form or a macro
