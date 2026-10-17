; expect: 5
; `vacant-slot` is its own slot (section 35): a `let` of `(slot-of
; vacant-slot)` sits where `vacant-slot` does, so a cell type naming its slot is the type of a fresh cell.
(def-adts $ (Pair2 : -> Type) enum (many P : (many (Nat) a) (many (Nat) b) -> (Pair2)))
(let ((many s)) (slot-of vacant-slot))
(def-fns _ $ (many go : (unique (Cell P (slot-of s) vacant-slot) u) -> (many (Nat) r))
  (let ((unique u2)) (cell-write unique u (P _ vacant-slot)))
  (let ((many p)) (share (u2 2 5)))
  (let-match many p (P _ y _))
  y)
(go (cell-alloc P))
