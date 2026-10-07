; error: `plain` has no `AtFn` proof in scope
(def-fns _ $ (many plain : (many (Nat) x) -> (many (Nat) r at x)) x)
(at-fn-of plain)
