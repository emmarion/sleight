; error: `g` is declared `at` `Zero`, which is not a function: it has type `(ValCtor -> (Nat))`
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (many g at Zero : (many (Nat) x) -> (many (Nat) r)) (delegate (inc x)))
0
