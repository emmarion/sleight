(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)) (many MkQ : -> (P)))
(def-fns _ $ (many mk : -> (unique (P) r)) (MkQ))
(def-fns _ $ (many f : -> (many (Nat) q))
  (match unique (mk) (((Nat) q))
    ((MkP a b c cell) a)
    (else (Zero))))
; error: tests/msg_else_unique_binder_one_bad.sl:6:5: error: this `match` `else` branch under `unique` expects 1 binder, got 0: expected `(unique _1 is _ at _1)`
; error: tests/msg_else_unique_binder_one_bad.sl:4:17: note: `_1` is anonymous, minted here
; error: tests/msg_else_unique_binder_one_bad.sl:1:13: note: type constructor `P` is declared here
