; error: 1 is a literal, not a name
(let ((many x)) (Cons (Nat) 1 (Nil (Nat))))
(comptime-match many x (Cons _ 1 t))
x
