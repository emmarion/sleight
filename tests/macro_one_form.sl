; needs: macro_lib
; error: must expand to one form here, and expanded to 2
(let ((many x)) (match many (splice 1 2) (((Nat) r)) (else 0)))
