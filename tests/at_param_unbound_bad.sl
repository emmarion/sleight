; error: tests/at_param_unbound_bad.sl:3:39: error: `at` is allowed only on return and match annotation entries
(def-lvl X)
(def-fns X $ (many f : (many (Nat) x) (many (Nat) y at nope) -> (many (Nat) r)) x)
