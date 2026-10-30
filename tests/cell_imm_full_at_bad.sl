; error: `imm` marks a store, and an `at`-wrapped invocation performs none
(def-adts $ (Two : -> Type)
  enum
  (many MkTwo : (many (U62) x) (many (U62) y) -> (Two)))

(def-fns _ $ (many f : (unique (Two) t) -> (unique (Two) r at t))
  (let-match unique t (MkTwo x y u))
  (at unique (u (imm (ImmPlaced _ (ImmU62) _ x (place-at-many _ x)) (ImmPlaced _ (ImmU62) _ x (place-at-many _ x))) x y)))
