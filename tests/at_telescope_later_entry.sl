; expect: 3
; A later entry of a parameter telescope, a return telescope or a match annotation sees the slot an earlier
; entry's `at` gives (sections 3, 36; audit/2026-10-07-review.md R2).
(def-adts $ (SameSlot : ((Slot) a) (a is b) -> Type)
  enum
  (many MkSame : (erased (Slot) a) -> (SameSlot a a)))
(def-fns _ $ (many f : (many (Nat) a) (many (Nat) b at a)
    (erased (SameSlot (slot-of a) (slot-of b)) eq) -> (many (Nat) r))
  a)
(def-fns _ $ (many g : (many (Nat) a) ->
    (many (Nat) r at a) (erased (SameSlot (slot-of a) (slot-of r)) eq))
  (values a (MkSame (slot-of a))))
(def-fns _ $ (many h : (many (Nat) x) -> (many (Nat) y))
  (let ((many r) (erased e))
    (match many x (((Nat) r at x) ((SameSlot (slot-of x) (slot-of r)) e))
      (else (values x (MkSame (slot-of x))))))
  (let ((many s) (erased e2)) (g r))
  (f r s (MkSame (slot-of r))))
(h 3)
