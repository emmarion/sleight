; expect: 5
; `vacant-slot` is the slot an allocation defaults to (AT_REDESIGN A1): a cell allocated with nothing has it
; in every slot, and a write of a vacant item leaves the slot vacant.
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(def-fns _ $ (many go : (unique (Cell P vacant-slot vacant-slot) u) -> (many (Nat) r))
  (let ((unique u2)) (cell-write u (P _ vacant-slot)))
  (let ((many p)) (u2 2 5))
  (let-match many p (P x y _))
  y)
(go (cell-alloc P))
