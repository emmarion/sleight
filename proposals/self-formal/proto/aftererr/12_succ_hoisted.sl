(compile-error "first")
(let ((many x)) (Succ (Zero)))
(comptime-match many x (Succ _))
