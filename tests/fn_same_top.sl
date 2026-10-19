; expect: (EONonErased _ _)
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-unique _ $ (unique bump : (many (Nat) n) -> (many (Nat) m)) (inc n))
(let ((many s)) (fn-same inc inc))
(comptime-match many s (EONonErased _ e))
(let ((many t)) (fn-same (share bump) (share bump)))
t
; fn-same: yes
