; error: expected a field name, got `(Succ h)`
(let ((many x)) (Cons (Nat) 1 (Nil (Nat))))
(let-match many x (Cons _ (Succ h) t))
x
