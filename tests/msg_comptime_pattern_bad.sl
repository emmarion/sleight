(def-adts $ (P : -> Type)
  enum
  (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(let ((many p)) (MkP (Zero) (Zero) (Zero)))
(comptime-match many p (MkP a b))
a
; error: tests/msg_comptime_pattern_bad.sl:5:24: error: a `comptime-match` pattern on `MkP` under `many` expects 3 or 4 binders, got 2: expected `(many (Nat) a) (erased (Nat) b) (many (Nat) c) (many (Cell MkP (slot-of a) (slot-of c)) _ at <**>)`
; error: tests/msg_comptime_pattern_bad.sl:3:3: note: value constructor `MkP` is declared here
