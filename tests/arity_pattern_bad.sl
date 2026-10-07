(def-adts $ (P3 : -> Type)
  enum
  (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P3)))
(def-fns _ $ (many k : (many (P3) p) -> (many (Nat) y))
  (match many p _ ((MkP a b) a)))
; error: tests/arity_pattern_bad.sl:5:20: error: a `match` branch on `MkP` under `many` expects 3 or 4 binders, got 2: expected `(many (Nat) a) (erased (Nat) b) (many (Nat) c) (many (Cell MkP (slot-of a) (slot-of c)) _ at <**>)`
; error: tests/arity_pattern_bad.sl:3:3: note: value constructor `MkP` is declared here
