; expect: 4
; A delegate may name the function it delegates to after its name (section 41), checked against the body.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))
(def-fns _ $ (many inc-noted at inc : (many (Nat) n) (erased (Nat) _note) -> (many (Nat) m))
  (delegate (inc n)))
(inc-noted 3 0)
