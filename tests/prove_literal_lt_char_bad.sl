; error: `prove-literal-lt` takes two numerals, got #\a
; prove-literal-lt refuses a character literal; its code's numeral stands for it.

(let ((erased q)) (prove-literal-lt #\a 98))
(Zero)
