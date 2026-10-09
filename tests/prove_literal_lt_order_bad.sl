; error: `prove-literal-lt`: 4 is not below 3
; prove-literal-lt reads the order from the spellings, so a branch's facts cannot reverse it.

(let ((erased q)) (prove-literal-lt 4 3))
(Zero)
