(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)) (many MkQ : -> (P)))
(def-fns _ $ (many mk : -> (many (P) r)) (MkQ))
(def-fns _ $ (many k : -> (many (Nat) y))
  (match many (mk) _ ((MkP a b) a) (else (Zero))))
; error: tests/msg_pattern_computed_bad.sl:4:23: error: a `match` branch on `MkP` under `many` expects 3 or 4 binders, got 2: expected `(many (Nat) a) (erased (Nat) b) (many (Nat) c) (many (Cell MkP (slot-of a) (slot-of c)) _ at <**>)`
; error: tests/msg_pattern_computed_bad.sl:1:32: note: value constructor `MkP` is declared here
