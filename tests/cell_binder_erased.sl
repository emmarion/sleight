; expect: 0
; A cell binder under an erased scrutinee (section 23): erased, with one slot per field whose label is
; non-erased, and at the scrutinee.
(def-fns _ $ (erased cell-at : (many (List (Nat)) xs) -> (erased (Nat) n))
  (let-match erased xs (Cons _ h t u) ((Nil _) 0))
  (let ((erased (Eq (Slot) (slot-of u) (slot-of xs)) p)) (Refl _ _))
  (let ((erased (Cell Cons (slot-of h) (slot-of t)) v)) u)
  h)
0
