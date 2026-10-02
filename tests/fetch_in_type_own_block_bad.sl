; error: unbound name `f`
(def-fns _
  ((many f : (many (Nat) n) -> (many (Nat) m))
    n)
  ((many g : (erased (Fn (level-of f) (many (Nat) n) -> (many (Nat) m)) h) -> (many (Nat) m))
    (Zero)))
(Zero)
