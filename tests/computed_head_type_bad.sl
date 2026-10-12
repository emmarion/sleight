(def-fns _ $ (many pick : (many (Special) s) -> (many (Special) r)) s)
(def-fns _ $ (many inc : (many (Nat) a) -> (many (Nat) b)) (Succ a))
(def-fns _ $ (many f : (many (Nat) a) -> (many (Nat) b))
  (let ((many ((pick Fn) (level-of inc) (many (Nat) a) -> (many (Nat) b)) g)) inc)
  (g a))
; error: tests/computed_head_type_bad.sl:4:16: error: a computed head in a type must be `Settled`, and this one is `Hypothetical`
