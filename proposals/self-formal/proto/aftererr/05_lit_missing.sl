(compile-error "first")
(let ((many x)) 3)
(comptime-match many x (Zero))
