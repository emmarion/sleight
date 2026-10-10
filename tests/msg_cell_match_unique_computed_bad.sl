(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many mk : -> (unique (Cell MkP vacant-slot vacant-slot) r)) (cell-alloc MkP))
(def-fns _ $ (many k : -> (many (Nat) r))
  (cell-match unique (mk) _ (MkP s1 u2) (Zero)))
; error: tests/msg_cell_match_unique_computed_bad.sl:4:29: error: `cell-match` on `MkP` under `unique` expects 3 binders, got 2: expected `(many vacant-slot is _) (many vacant-slot is _) (unique __1 is _ at __1)`
; error: tests/msg_cell_match_unique_computed_bad.sl:4:22: note: `__1` is anonymous, minted here
; error: tests/msg_cell_match_unique_computed_bad.sl:1:32: note: value constructor `MkP` is declared here
