; expect: 0
; A `let` forwarding from a level takes over its introduction order and its level-mint marker (section 19), so
; both arguments of `prove-predates` may be forwarding binders.
(def-lvl M)
(let ((erased M2)) M)
(def-lvl L)
(let ((erased L2)) L)
(let ((erased p)) (prove-predates M2 L2))
0
