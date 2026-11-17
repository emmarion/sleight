(let ((many y)) (Succ (Zero)))
(compile-error "first")
(let ((many x)) y)
(comptime-match many x (Succ _))
