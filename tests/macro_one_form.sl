; needs: macro_lib
; error: must expand to one form here, and expanded to 2
(let ((many x) (many y)) (values 1 (splice 2 3)))
