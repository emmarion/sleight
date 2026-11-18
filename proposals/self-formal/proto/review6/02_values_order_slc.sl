(def-lvl G)
(def-fns G $ (many g : (many (Nat) x) -> (many (Nat) r)) (Succ x))
(def-fns G $ (many h : (many (Nat) x) -> (many (Nat) r)) (Succ $ Succ x))
(def-fns _ $ (many pick : -> (many (Fn G (many (Nat) x) -> (many (Nat) r)) f)) g)
(def-fns _ $ (many top : (many (Nat) n) -> (many (Nat) r)) (values ((pick) (h n) ) ))
(def-fns _ $ (many top2 : (many (Nat) n) -> (many (Nat) a) (many (Nat) b)) (values (g (h n)) (h (g n))))
(def-fns _ $ (many main : -> (many (Nat) r)) (let ((many a) (many b)) (top2 1)) (top a))
main
