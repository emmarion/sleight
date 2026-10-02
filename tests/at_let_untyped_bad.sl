; error: tests/at_let_untyped_bad.sl:4:9: error: `at` is allowed only on return and match annotation entries
(def-lvl X)
(def-fns X $ (many f : (many (Nat) x) -> (many (Nat) r))
  (let ((many y at x)) x)
  y)
