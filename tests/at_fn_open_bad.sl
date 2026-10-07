; error: is not an `AtFn` proof
(def-fns _ $ (many same : (many (Nat) x) -> (many (Nat) r at x)) x)
(let ((erased p)) (coercible-refl (Shared) same))
(open-at-fn p)
