(def-adts $ (P : -> Type) enum (many MkP : (many (Nat) a) (erased (Nat) b) (many (Nat) c) -> (P)) (many MkQ : -> (P)))
(def-fns _ $ (many f : (unique (P) p) -> (many (Nat) q) (unique (P) r))
  (match unique p (((Nat) q) ((P) r at p))
    ((MkP a b c cell) (values a (cell a b c)))
    (else p2 (values (Zero)))))
; error: tests/msg_else_values_at_bad.sl:5:14: error: the enclosing `match` expects 2 return values, got 1: expected `(many (Nat) q) (unique (P) r at p)`
; error: tests/msg_else_values_at_bad.sl:3:19: note: the return annotation of the enclosing `match` is here
