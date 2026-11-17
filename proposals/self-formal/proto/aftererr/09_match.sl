(let ((many y)) (Succ (Zero)))
(compile-error "first")
(let ((many x)) (match many y (((Bool) _)) ((Succ _) (BFalse))))
(comptime-match many x (BFalse))
