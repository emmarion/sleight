; error: type mismatch: expected `(Settled (MMany) __?1 __?2)`, got `(Settled (MErased) (Nat) 40)`
(let ((many k)) 40)
(settled-value _ _ (settled-of erased k))
