(def-adts $ (P3 : -> Type)
  enum
  (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P3)))
(def-fns _ $ (many k : (many (P3) p) -> (many (Nat) y))
  (match many p _ ((MkP a b) a)))
; error: tests/arity_pattern_bad.sl:5:<**>: error: `MkP` expects 3 fields, got 2
; error: tests/arity_pattern_bad.sl:3:3: note: `MkP` takes `(many (Nat) a) (erased (Nat) b) (many (Nat) c)`
