(def-fns _ $ (many f : (many (Nat) a) (many (Nat) b) -> (many (Nat) r)) (nat-add a b))
(def-fns _ $ (many g : (many (Nat) a) -> (many (Nat) r) (many (Nat) s)) (values (f a a) (f (Succ a) a)))
(def-fns _ $ (many h : (many (Nat) a) -> (many (Pair (Nat) (Nat)) r)) (MkPair _ _ (f a a) (f a 1)))
(def-fns _ $ (many main : -> (many (Nat) r)) (let ((many x) (many y)) (g 3)) (let-match many (h x) (MkPair _ _ p q)) (f y q))
main
