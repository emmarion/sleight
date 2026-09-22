; error: is not a strict subterm of
; A slot's content is not a subterm of the slot. SlotHolds is a value constructor, the production section 8's
; walk does enter, but its argument is a direct variable reference (U2a) standing for a location's contents
; rather than structure, so the walk must stop at it: a cell-write can store anything into a slot.

(def-fns _ $ (many probe : (many (Nat) x) -> (many (Nat) r))
  (let ((erased p)) (prove-subterm x (SlotHolds x)))
  x)
