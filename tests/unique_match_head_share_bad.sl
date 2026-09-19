; error: many value
(def-lvl answer-level)
(def-fns _ $ many choose : (many (Nat) tag) (unique (UniqueFn answer-level -> (many (Nat) r)) f) -> (many (Nat) r)
  ((match many tag (((UniqueFn answer-level -> (many (Nat) r)) g))
     ((Zero) (share f))
     ((Succ n) (share f)))))
