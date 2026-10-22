; error: tests/zero_size_tail.sl:3:43: error: `tail` in an erased position
(def-fns _ $ (many g : (many (Nat) _n) ->) (values))
(def-fns _ $ (many f : (many (Nat) n) ->) (tail (g n)))
(Zero)
