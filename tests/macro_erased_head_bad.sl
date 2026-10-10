; needs: macro_lib
; error: `em` is an erased macro, and only a non-erased one is expanded
(let ((erased em)) swap)
(em nat-add 1 2)
