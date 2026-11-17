(let ((many y)) (Succ (Succ (Zero))))
(compile-error "first")
(comptime-match many y (Succ p))
(comptime-match many p (Zero))
