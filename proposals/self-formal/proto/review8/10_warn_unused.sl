(compile-error "first")
(def-fns _ $ (many f : (many (Nat) n) (many (Nat) k) -> (many (Nat) m)) (Succ n))
(compile-warn "end")
