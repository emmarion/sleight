; error: tests/at_erased_return_bad.sl:3:42: error: `at` needs an entry declared `many` or `unique`
(def-lvl X)
(def-fns X $ (many f : (many (Nat) x) -> (erased (Nat) r at x)) x)
