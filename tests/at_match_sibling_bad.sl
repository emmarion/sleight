; error: tests/at_match_sibling_bad.sl:3:110: error: `at` must name an argument or a closed-over variable
(def-lvl X)
(def-fns X $ (many f : (many (Nat) x) -> (many (Nat) r) (many (Nat) s)) (match many x (((Nat) a) ((Nat) b at a)) ((Zero) (values x x)) ((Succ _) (values x x))))
