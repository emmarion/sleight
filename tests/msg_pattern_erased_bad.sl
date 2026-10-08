(def-adts $ (P : -> Type)
  enum
  (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many k : (many (P) p) -> (erased (Nat) y))
  (match erased p _ ((MkP a b) a)))
(Zero)
; error: tests/msg_pattern_erased_bad.sl:5:22: error: a `match` branch on `MkP` under `erased` expects 3 or 4 binders, got 2: expected `(erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Cell MkP (slot-of a) (slot-of c)) _ at p)`
; error: tests/msg_pattern_erased_bad.sl:3:3: note: value constructor `MkP` is declared here
