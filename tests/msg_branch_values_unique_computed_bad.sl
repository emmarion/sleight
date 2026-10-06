(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)) (many MkQ : -> (P)))
(def-fns _ $ (many mk : -> (unique (P) r)) (MkQ))
(def-fns _ $ (many f : -> (many (Nat) q) (unique (P) r))
  (match unique (mk) (((Nat) q) ((P) r))
    ((MkP a b c cell) (values a))
    (else p2 (values (Zero) p2))))
; error: tests/msg_branch_values_unique_computed_bad.sl:5:23: error: the enclosing `match` expects 2 return values, got 1: expected `(many (Nat) q) (unique (P) r)`
; error: tests/msg_branch_values_unique_computed_bad.sl:4:22: note: the return annotation of the enclosing `match` is here
