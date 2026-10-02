(let ((many otherwise)) else)
(Succ (otherwise 3))
; error: `(otherwise ...)` is not an expression
; error: hint: `otherwise` heads the match branch for every constructor not listed
; error: hint: usage: (otherwise <statement> ... <value>)
