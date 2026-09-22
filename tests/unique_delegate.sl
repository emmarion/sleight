; expect: 1
(def-fns _ $ (many id : (many (Nat) x) -> (many (Nat) r)) x)
(def-unique _ $ (unique d : (many (Nat) x) -> (many (Nat) r)) (delegate (id x)))
(let ((erased p)) (coercible-of (delegate-of d)))
(let ((many f)) (coerce d p))
(f (Succ (Zero)))
