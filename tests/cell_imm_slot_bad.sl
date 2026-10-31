; needs: ../std/immediate
; error: type mismatch
(def-adts $ (Two : -> Type)
  enum
  (many MkTwo : (many (U62) x) (many (U62) y) -> (Two)))

(def-fns _ $ (many f : (unique (Two) t) (many (U62) z) -> (unique (Two) r at t))
  (let-match unique t (MkTwo x y u))
  (u (imm (ImmPlaced _ _ (imm-of _ (ImmU62) y) _ (place-at-many _ y)) (ImmPlaced _ _ (imm-of _ (ImmU62) z) _ (place-at-many _ z))) z y))
