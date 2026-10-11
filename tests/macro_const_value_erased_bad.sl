; error: type mismatch: expected `(Const (MMany) __?1 __?2)`, got `(Const (MErased) (Nat) 40)`
(let ((many k)) 40)
(const-value _ _ (constant-of erased k))
