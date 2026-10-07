(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)))
(def-fns _ $ (many mk : -> (unique (P) r)) (MkP (Zero) (Zero) (Zero)))
(def-fns _ $ (many k : -> (many (Nat) y))
  (let-match unique (mk) (MkP a b))
  a)
; error: tests/msg_let_match_computed_bad.sl:4:26: error: a `let-match` pattern on `MkP` under `unique` expects 3 or 4 binders, got 2: expected `(many (Nat) a) (erased (Nat) b) (many (Nat) c) (unique (Cell MkP (slot-of a) (slot-of c)) _ at _1)`
; error: tests/msg_let_match_computed_bad.sl:4:21: note: `_1` is anonymous, minted here
; error: tests/msg_let_match_computed_bad.sl:1:32: note: value constructor `MkP` is declared here
