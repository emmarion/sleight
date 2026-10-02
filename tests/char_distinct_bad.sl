; error: `distinct`: #\a and #\b do not canonicalize equally here, so there is nothing to refute
; distinct names character literals as they are spelled, not by their codes.

(let ((erased q)) (distinct #\a #\b))
(Zero)
