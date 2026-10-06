(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many k : (unique (Cell MkP (SlotVacant) (SlotVacant)) u) -> (many (P) r))
  (u (Zero) (Zero) (Nil (Nat))))
; error: tests/msg_cell_invoke_argtype_bad.sl:3:20: error: argument 3, `c`, of `u`, a `Cell` of `MkP`: type mismatch: expected `(Nat)`, got `(List (Nat))`
; error: tests/msg_cell_invoke_argtype_bad.sl:1:32: note: value constructor `MkP` is declared here
