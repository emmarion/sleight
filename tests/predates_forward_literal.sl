; expect: 0
; A `let` forwarding from a literal keeps an introduction order of its own, the literal having none.
(let ((many three)) 3)
(def-lvl L)
(let ((erased p)) (prove-predates three L))
0
