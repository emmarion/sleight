(let ((many y)) (Zero))
(compile-error "first")
(let ((many x)) (Succ y))
(comptime-match many x (Succ _))
