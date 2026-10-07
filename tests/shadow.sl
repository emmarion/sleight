; needs: list
; expect: 1
; A special form renamed through a state-forwarding let (sections 6, 19).

(let ((many define)) let)
(define ((many one)) (Succ (Zero)))
one
