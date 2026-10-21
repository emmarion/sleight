; error: `plain` has no `AtFn` proof in scope
(def-fns _ $ (many plain : (many (Nat) x) -> (many (Nat) r at x)) x)
(let ((erased p))
  (match erased (Zero) (((AtFn (Fn (level-of plain) (many (Nat) x) -> (many (Nat) r at x)) plain) q))
    (else (at-fn-of plain))))
