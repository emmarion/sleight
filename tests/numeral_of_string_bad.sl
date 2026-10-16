; error: carries no `Numeral` proof
; numeral-of yields a numeral's Numeral proof (section 45); a string literal has none.

(let ((erased q)) (numeral-of "ab"))
(Zero)
