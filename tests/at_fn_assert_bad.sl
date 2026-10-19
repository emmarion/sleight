; error: `plain` is not an at-function here: no `AtFn` proof for it is open
(def-fns _ $ (many plain : (many (Nat) x) -> (many (Nat) r at x)) x)
(at erased (plain 5))
