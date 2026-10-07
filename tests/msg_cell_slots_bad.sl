(def-adts $ (P : -> Type)
  enum
  (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many k : (unique (Cell MkP vacant-slot) u) -> (many (Nat) y)) (Zero))
(Zero)
; error: tests/msg_cell_slots_bad.sl:4:32: error: the type former `Cell` of `MkP` expects 2 slots, got 1: expected one for each non-erased field of `(many (Nat) a) (erased (Nat) b) (many (Nat) c)`
; error: tests/msg_cell_slots_bad.sl:3:3: note: value constructor `MkP` is declared here
