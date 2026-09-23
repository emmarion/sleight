; error: `numeral-of` takes a literal
; numeral-of resolves a literal by its own spelling, so a name canonicalizing to one is not accepted.

(let ((many x)) 5)
(let ((erased r)) (numeral-of x))
(Zero)
