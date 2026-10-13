; error: tests/at_let_bad.sl:4:9: error: `at` is allowed only on function telescope and match annotation entries
(def-lvl X)
(def-fns X $ (many f : (many (Nat) x) -> (many (Nat) r))
  (let ((many (Nat) y at x)) x)
  y)
