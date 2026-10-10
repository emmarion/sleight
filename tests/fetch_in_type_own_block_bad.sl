; error: unbound name `f`
; A signature sees only the functions before it in its block (section 53).
(def-fns _
  ((many g : (erased (Fn (level-of f) (many (Nat) n) -> (many (Nat) m)) h) -> (many (Nat) m))
    (Zero))
  ((many f : (many (Nat) n) -> (many (Nat) m))
    n))
(Zero)
