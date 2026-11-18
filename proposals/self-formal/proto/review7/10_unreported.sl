(compile-error "first")
;! suppress warn Zero
;! restore warn Zero
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (many g : (many (Nat) n) -> (many (Nat) m)) (f (predates _) n))
(compile-warn "end")
