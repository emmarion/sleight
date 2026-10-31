; needs: ../std/immediate
; error: `imm` marks a store into a cell, and `cell-alloc` fills a fresh one
(def-adts $ (Two : -> Type)
  enum
  (many MkTwo : (many (U62) x) (many (U62) y) -> (Two)))

(def-fns _ $ (many f : (many (U62) z) -> (unique (Cell MkTwo (slot-of z) vacant-slot) r))
  (cell-alloc (MkTwo (imm (ImmVacant) (ImmPlaced _ _ (imm-of _ (ImmU62) z) _ (place-at-many _ z))) (slot-of z) _)))
