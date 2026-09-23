; error: expected a `Delegate` proof
(def-fns _ $ (many id : (many (Nat) x) -> (many (Nat) r)) x)
(let ((erased p)) (coercible-of (coercible-refl (Shared) id)))
(Zero)
