(compile-error "first")
(let ((many x)) (Ok (Nat) 1))
(comptime-match many x (Ok _ v))
