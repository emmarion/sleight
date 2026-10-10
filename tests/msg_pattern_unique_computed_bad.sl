(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)) (many MkQ : -> (P)))
(def-fns _ $ (many mk : -> (unique (P) r)) (MkQ))
(def-fns _ $ (many f : -> (many (Nat) q))
  (match unique (mk) (((Nat) q))
    ((MkP a b) a)
    (else p2 (Zero))))
; error: tests/msg_pattern_unique_computed_bad.sl:5:6: error: a `match` branch on `MkP` under `unique` expects 3 or 4 binders, got 2: expected `(many (Nat) a) (erased (Nat) b) (many (Nat) c) (unique (Cell MkP (slot-of a) (slot-of c)) _ at __1)`
; error: tests/msg_pattern_unique_computed_bad.sl:4:17: note: `__1` is anonymous, minted here
; error: tests/msg_pattern_unique_computed_bad.sl:1:32: note: value constructor `MkP` is declared here
