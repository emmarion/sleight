(let ((many y)) (Succ (Zero)))
(compile-error "first")
(let-match many y (Succ p))
(comptime-match many p (Zero))
