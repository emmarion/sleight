; error: `slot-of` in a constructor's telescope cannot name `x`, bound by a telescope still being written
; The variable is a parameter of the telescope the `ValCtor` type is written in.
(def-fns _ $ (many f : (many (Nat) x) (erased (ValCtor (many (Eq (Slot) (slot-of x) (slot-of x)) e) -> (Unit)) c) -> (many (Nat) r))
  x)
