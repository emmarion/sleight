; error: type mismatch
(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (List (Nat)) xs) -> (Box)))

(def-fns _ $ (many f : (unique (Box) b) (many (List (Nat)) ys) -> (unique (Box) r at b))
  (let-match unique b (MkBox xs u))
  (u (imm (ImmPlaced _ (ImmU62) _ xs (place-at-many _ xs)) (ImmPlaced _ (ImmU62) _ ys (place-at-many _ ys))) ys))
