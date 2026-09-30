; error: malformed `tail` form
(def-lvl L1)
(def-lvl L2)
(let ((erased p)) (prove-predates L1 L2))
(def-fns L1 $ (many f : (many (Nat) x) -> (many (Nat) r)) x)
(def-fns L2 $ (many g : (many (Nat) x) -> (many (Nat) r)) (tail (f (predates p) x) x))
(g (Zero))
