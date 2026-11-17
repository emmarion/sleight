(compile-error "first")
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(let ((many x)) (f (Zero)))
(comptime-match many x (Zero))
