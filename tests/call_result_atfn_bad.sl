; error: `plain` has no `AtFn` proof in scope
(def-fns _ $ (many plain : (many (Nat) x) -> (many (Nat) r at x)) x)
(def-fns _ $ (many pass : (erased (AtFn (Fn (level-of plain) (many (Nat) x) -> (many (Nat) r at x)) plain) p) -> (erased (AtFn (Fn (level-of plain) (many (Nat) x) -> (many (Nat) r at x)) plain) q)) p)
(let ((erased q)) (pass (at-fn-of plain)))
