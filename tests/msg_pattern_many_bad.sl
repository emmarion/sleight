(def-adts $ (P : -> Type)
  enum
  (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many k : (many (P) p) -> (many (Nat) y))
  (match many p _ ((MkP a b) a)))
; error: tests/msg_pattern_many_bad.sl:5:20: error: a `match` branch on `MkP` under `many` expects 3 binders, got 2: expected `(many (Nat) a) (erased (Nat) b) (many (Nat) c)`
; error: tests/msg_pattern_many_bad.sl:3:3: note: value constructor `MkP` is declared here
