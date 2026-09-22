; error: unexpected )
; warns: tests/indent_surplus_bad.sl:7:24: warning: a ) here closes more than is open (surplus ))
; A ) closing more than is open is reported where it sits, and leaves the depth at zero, so the lines after
; it are still checked against the count of forms actually open.

(def-lvl A)
(let ((many x)) (Zero)))
x
