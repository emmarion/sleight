; error: `inner` expects 2 arguments, got 1: expected `(many (Nat) x) (many (Nat) y at z)`
; A type whose `at` names a variable of the enclosing scope is shown with that variable.
(def-fns _ $ (many outer : (many (Nat) z) -> (many (Nat) out))
  (def-fns _ $ (many inner : (many (Nat) x) (many (Nat) y at z) -> (many (Nat) q at z))
    z)
  (inner 1))
