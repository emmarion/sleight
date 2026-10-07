(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many k : (many (Cell MkP vacant-slot vacant-slot) u) -> (many (Nat) r))
  (cell-match many u _ (MkP s1) (Zero)))
; error: tests/msg_cell_match_many_bad.sl:3:24: error: `cell-match` on `MkP` under `many` expects 2 binders, got 1: expected `(many vacant-slot is _) (many vacant-slot is _)`
; error: tests/msg_cell_match_many_bad.sl:1:32: note: value constructor `MkP` is declared here
