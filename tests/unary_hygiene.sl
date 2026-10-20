; expect: 0
; unary's expansion names its let-match mode through a handle, so a program that shadows `erased` still gets
; the rule.
(def-fns _ $ (many four-succ : (erased (Eq (Nat) 4 (Succ (Succ (Succ (Succ (Zero)))))) _p) -> (many (Nat) r)) (Zero))
(let ((many erased)) 0)
(unary 4)
(four-succ (Refl _ 4))
; warns: tests/unary_hygiene.sl:5:7: warning: declaration of `erased` shadows a built-in
