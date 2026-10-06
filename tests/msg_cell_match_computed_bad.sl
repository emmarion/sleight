(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many mk : -> (unique (Cell MkP (SlotVacant) (SlotVacant)) r)) (cell-alloc MkP))
(def-fns _ $ (many k : -> (many (Nat) r))
  (cell-match many (share (mk)) _ (MkP s1) (Zero)))
; error: tests/msg_cell_match_computed_bad.sl:4:35: error: `cell-match` on `MkP` under `many` expects 2 binders, got 1: expected `(many (SlotVacant) is _) (many (SlotVacant) is _)`
; error: tests/msg_cell_match_computed_bad.sl:1:32: note: value constructor `MkP` is declared here
