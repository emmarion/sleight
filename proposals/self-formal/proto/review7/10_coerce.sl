(let ((many y)) (Succ (Zero)))
(compile-error "first")
(let ((many x)) (coerce y (coercible-refl (Shared) y)))
(comptime-match many x (Succ _))
