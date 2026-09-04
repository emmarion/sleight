; needs: list
; expect: (Succ (Zero))
; A special form renamed through a state-forwarding let (sections 4, 9).

(let (many define) let)
(define (many one) (Succ (Zero)))
one
