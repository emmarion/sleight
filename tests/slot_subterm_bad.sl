; error: is not a strict subterm of
; A slot's content is not a subterm of the slot: `(slot-of x)` is the slot's own atom in the fact table
; (AT_REDESIGN A6), which has no structure for section 8's walk to enter, and a cell-write can store anything
; into a slot.

(def-fns _ $ (many probe : (many (Nat) x) -> (many (Nat) r))
  (let ((erased p)) (prove-subterm x (slot-of x)))
  x)
