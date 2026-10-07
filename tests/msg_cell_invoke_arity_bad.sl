(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many k : (unique (Cell MkP vacant-slot vacant-slot) u) -> (unique (P) r))
  (u (Zero) (Zero)))
; error: tests/msg_cell_invoke_arity_bad.sl:3:3: error: `u`, a `Cell` of `MkP`, expects 3 arguments, got 2: expected `(many (Nat) a) (erased (Nat) b) (many (Nat) c)`
; error: tests/msg_cell_invoke_arity_bad.sl:1:32: note: value constructor `MkP` is declared here
