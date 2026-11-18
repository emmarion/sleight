(def-fns _ $ (many f : -> (many (Bool) r)) (BFalse))
(compile-error "first")
(let ((many x)) (native-compute f))
(comptime-match many x (BFalse))
