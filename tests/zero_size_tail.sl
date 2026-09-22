; expect: 0
(def-fns _ $ (many g : (many (Nat) n) ->) (values))
(def-fns _ $ (many f : (many (Nat) n) ->) (tail (g n)))
(let () (f (Zero)))
(Zero)
