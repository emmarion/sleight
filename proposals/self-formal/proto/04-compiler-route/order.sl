(def-fns _ $ (many f : (many (Nat) a) (many (Nat) b) -> (many (Nat) r)) (nat-add a b))
(def-fns _ $ (many g : (many (Nat) a) -> (many (Nat) r)) (f (f a a) (f (Succ a) a)))
(def-fns _ $ (many main : -> (many (Nat) r)) (g 3))
main
