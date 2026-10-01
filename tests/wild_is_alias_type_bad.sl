; error: type mismatch: expected `(Bool)`, got `(Nat)`
; The type printed for an is return instantiated with an alias-typed argument is the canonical one.

(let ((erased Alias)) (Nat))

(def-lvl L)
(def-fns L $ (many same : (many (Nat) a) -> (many a is r))
  a)

(let ((many Alias x)) (Succ (Zero)))
(let ((erased (Bool) r)) (same x))
(Zero)
