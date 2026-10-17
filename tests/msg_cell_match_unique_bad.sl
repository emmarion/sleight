(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many k : (unique (Cell MkP vacant-slot vacant-slot) u) -> (many (Nat) r))
  (cell-match unique u _ (MkP s1) (Zero)))
; error: tests/msg_cell_match_unique_bad.sl:3:26: error: `cell-match` on `MkP` under `unique` expects 2 or 3 binders, got 1: expected `(many vacant-slot is _) (many vacant-slot is _) (unique u is _ at u)`
; error: tests/msg_cell_match_unique_bad.sl:1:32: note: value constructor `MkP` is declared here
