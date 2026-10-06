(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)) (many MkQ : -> (P)))
(def-fns _ $ (many f : (unique (P) p) -> (many (Nat) q) (many (Nat) r))
  (match unique p (((Nat) q) ((Nat) r))
    ((MkP a b c cell) (values a c))
    (else (values (Zero) (Zero)))))
; error: tests/msg_else_unique_binder_bad.sl:5:5: error: this `match` `else` branch under `unique` expects 1 binder, got 0: expected `(unique p is _ at p)`
; error: tests/msg_else_unique_binder_bad.sl:1:13: note: type constructor `P` is declared here
