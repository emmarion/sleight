; error: `fn-same` takes functions of one type, and `inc` : `(Fn (level-of inc) (many (Nat) n) -> (many (Nat) m))` and `inc-noted` : `(Fn (level-of inc-noted) (many (Nat) n) (erased (Nat) note) -> (many (Nat) m))` are not
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (many inc-noted at inc : (many (Nat) n) (erased (Nat) note) -> (many (Nat) m))
  (delegate (inc n)))
(let ((many s)) (fn-same inc inc-noted))
