; error: `prove-literal-lt`: 3 is not below 3
; prove-literal-lt refuses one literal given twice.

(let ((erased q)) (prove-literal-lt 3 3))
(Zero)
