; expect: 2
; The prelude's primitives carry their specifications (section 41): add returns an Add, nat-mod a Mod with the
; bound, add-u8 a U8Add relating the fields, append an Append, and trim's return is its argument to the checker.

(let ((many three)) (Succ (Succ (Succ (Zero)))))
(let ((many five)) (Succ (Succ three)))
(let ((many eight) (erased (Add three five eight) pa)) (add three five))
(let ((many two) (erased (Lt two three) lt) (erased (Mod eight three two) pm)) (nat-mod eight three (LtZ (Succ (Succ (Zero))))))

(let ((many d)) (lt-dec three u8-modulus))
(comptime-match many d (Yes a b p3))
(let ((many u3)) (MkU8 three p3))
(let ((many u6) (erased (U8Add u3 u3 u6) w)) (add-u8 u3 u3))
(let-match many u6 (MkU8 six p6))
(let-match erased w (MkU8Add n m r pn pm pr s ps q))
(let ((erased (Add three three s) ps2)) ps)
(let ((erased (Mod s u8-modulus six) q2)) q)

(let ((many hello)) "ab")
(let ((many t)) (trim hello))
(let ((erased (Eq (String) hello t) e)) (Refl (String) hello))
(let ((many tt) (erased (Append hello t tt) pp)) (append hello t))
two
