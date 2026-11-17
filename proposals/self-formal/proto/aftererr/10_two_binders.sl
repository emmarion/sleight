(compile-error "first")
(let ((many a) (many b)) (values (BFalse) 5))
(comptime-match many a (BFalse))
(comptime-match many b (Succ _))
