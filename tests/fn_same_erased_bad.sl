; error: `fn-same` in an erased position
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (many f : -> (many (Nat) r))
  (let ((erased s)) (fn-same inc inc))
  0)
