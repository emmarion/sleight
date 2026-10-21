; error: `id` has no `Delegate` proof in scope
(def-fns _ $ (many id : (many (Nat) x) -> (many (Nat) r)) x)
(def-fns _ $ (many yes : (many (Nat) _x) -> (many (Bool) r)) (BTrue))
(let ((erased d))
  (match erased (Zero) (((Delegate (Shared) (Fn (level-of id) (many (Nat) x) -> (many (Nat) r)) id (Shared) (Fn (level-of yes) (many (Nat) x) -> (many (Bool) r)) yes) q))
    (else (delegate-of id))))
(let ((many (Fn (level-of yes) (many (Nat) x) -> (many (Bool) r)) g)) (coerce id (coercible-of d)))
(g 7)
