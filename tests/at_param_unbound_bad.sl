; error: tests/at_param_unbound_bad.sl:3:56: error: unbound name `nope`
(def-lvl X)
(def-fns X $ (many f : (many (Nat) x) (many (Nat) y at nope) -> (many (Nat) r)) x)
