; error: `imm` marks a store, and `_` stores nothing
(def-adts $ (Two : -> Type)
  enum
  (many MkTwo : (many (U62) x) (many (U62) y) -> (Two)))

(def-fns _ $ (many f : (unique (Two) t) (many (U62) z) -> (unique (Two) r at t))
  (let-match unique t (MkTwo x y u))
  (let ((unique u2)) (cell-write unique u (MkTwo (imm (ImmPlaced _ (ImmU62) _ x (place-at-many _ x)) (ImmPlaced _ (ImmU62) _ z (place-at-many _ z))) _ _)))
  (at unique (u2 x y)))
