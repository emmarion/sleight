; error: `fn-same` needs `--fn-same` (OPEN.md 36)
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(let ((many s)) (fn-same inc inc))
