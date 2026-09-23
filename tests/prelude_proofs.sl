; expect: 2
; The prelude's primitives carry their specifications (section 41): add returns an Add, nat-mod a Mod with the
; bound, append an Append, and trim's return is its argument to the checker.

(let ((many three)) (Succ (Succ (Succ (Zero)))))
(let ((many five)) (Succ (Succ three)))
(let ((many sum8) (erased (Add three five sum8) pa)) (add three five))
(let ((many two) (erased (Lt two three) lt) (erased (Mod sum8 three two) pm)) (nat-mod sum8 three (LtZ (Succ (Succ (Zero))))))

(let ((many hello)) "ab")
(let ((many t)) (trim hello))
(let ((erased (Eq (String) hello t) e)) (Refl (String) hello))
(let ((many tt) (erased (Append hello t tt) pp)) (append hello t))
two
