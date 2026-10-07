; error: an `erased` function cannot be an at-function
(def-fns _ $ (erased at f : (many (Nat) p) -> (many (Nat) r at p)) p)
