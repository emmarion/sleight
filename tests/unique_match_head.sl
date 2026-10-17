; expect: 1
(def-lvl answer-level)
(def-unique answer-level $ (unique answer : -> (many (Nat) r)) (Succ (Zero)))
(def-fns _ $ (many choose : (many (Nat) tag) (unique (UniqueFn answer-level -> (many (Nat) r)) f) -> (many (Nat) r))
  ((match many tag (((UniqueFn answer-level -> (many (Nat) r)) g))
     ((Zero) f)
     ((Succ _) f))))
(choose (Zero) answer)
