(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many k : (unique (Cell MkP (SlotVacant) (SlotVacant)) u) -> (unique (Cell MkP (SlotVacant) (SlotVacant)) r))
  (cell-write u (MkP _)))
; error: tests/msg_cell_write_items_bad.sl:3:17: error: `cell-write` of `MkP` expects 2 slot items, got 1: expected one for each non-erased field of `(many (Nat) a) (erased (Nat) b) (many (Nat) c)`
; error: tests/msg_cell_write_items_bad.sl:1:32: note: value constructor `MkP` is declared here
