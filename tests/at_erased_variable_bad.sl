; error: tests/at_erased_variable_bad.sl:3:61: error: `at` needs a variable declared `many` or `unique`
(def-lvl X)
(def-fns X $ (many f : (erased (Nat) x) -> (many (Nat) r at x)) 0)
