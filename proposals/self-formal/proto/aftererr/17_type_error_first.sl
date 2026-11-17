(let ((many y)) (Succ (Zero)))
(let ((many x)) (match many y (((Bool) _)) ((Zero) (BTrue)) ((Succ _) (BFalse))))
(comptime-match many x (BFalse))
(compile-error "end")
