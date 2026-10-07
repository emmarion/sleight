(def-adts $ (P : -> Type)
  enum
  (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many k : (unique (P) p) -> (many (Nat) y))
  (match unique p _ ((MkP a b) a)))
; error: tests/msg_pattern_unique_bad.sl:5:22: error: a `match` branch on `MkP` under `unique` expects 3 or 4 binders, got 2: expected `(many (Nat) a) (erased (Nat) b) (many (Nat) c) (unique (Cell MkP (slot-of a) (slot-of c)) _ at p)`
; error: tests/msg_pattern_unique_bad.sl:3:3: note: value constructor `MkP` is declared here
