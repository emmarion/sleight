; expect: 7
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))

(def-fns _ $ (many twice : (many (Fn (level-of inc) (many (Nat) x) -> (many (Nat) y)) f)
    (many (Nat) n) -> (many (Nat) m))
  (f $ f n))

(twice inc 5)
