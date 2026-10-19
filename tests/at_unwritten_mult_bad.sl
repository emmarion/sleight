; error: `at` around a call or a `Cell` invocation names the multiplicity its head is taken at
(def-fns _ $ (many at same : (many (Nat) x) -> (many (Nat) r at x)) x)
(at (same 5))
