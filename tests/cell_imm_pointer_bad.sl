; needs: ../std/immediate
; error: type mismatch
(def-adts $ (Box : -> Type)
  enum
  (many MkBox : (many (List (Nat)) xs) -> (Box)))

(def-fns _ $ (many f : (unique (Box) b) (many (List (Nat)) ys) -> (unique (Box) r at b))
  (let-match unique b (MkBox xs u))
  (u (imm (ImmPlaced _ _ (imm-of _ (ImmU62) xs) _ (place-at-many _ xs)) (ImmPlaced _ _ (imm-of _ (ImmU62) ys) _ (place-at-many _ ys))) ys))
