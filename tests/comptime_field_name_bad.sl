; error: expected a field name, got `(Succ h)`
(let ((many x)) (Cons (Nat) 1 (Nil (Nat))))
(comptime-match many x (Cons _ (Succ h) t))
(comptime-match many t (Nil _))
x
