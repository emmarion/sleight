; expect: 8
(def-fns _ $ (many pick : (many (Special) s) -> (many (Special) r)) s)
(def-fns _ $ (many inc : (many (Nat) a) -> (many (Nat) b)) (Succ a))
(let ((many F)) (pick Fn))
(def-fns _ $ (many twice : (many (F (level-of inc) (many (Nat) a) -> (many (Nat) b)) g) (many (Nat) n) -> (many (Nat) r)) (g $ g n))
(twice inc 6)
