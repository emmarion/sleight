; error: value mismatch
; A cell is tied to the constructor it was allocated or destructured at: cell-write takes the same
; constructor its cell's type names, so a block cannot be rewritten as a different constructor's, even
; one of the same non-erased arity. cell_map_retype.sl is what a cell does admit, a change of the type
; constructor's arguments under the same value constructor.

(def-adts $ A2 : -> Type enum (many MkA : (many (Nat) x) (many (Nat) y) -> (A2)))
(def-adts $ B2 : -> Type enum (many MkB : (many (Nat) p) (many (Nat) q) -> (B2)))

(def-fns _ $ many convert : (unique (A2) a) -> (unique (B2) b)
  (match unique a _
    ((MkA x y cell)
      (let (unique cell2) (cell-write cell (MkB (SlotHolds y) (SlotHolds x))))
      (cell2 y x))))
convert
