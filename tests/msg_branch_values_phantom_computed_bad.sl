(def-adts $ (P : -> Type) enum (erased Ph : -> (P)) (many MkQ : -> (P)))
(def-fns _ $ (many mk : -> (many (P) r)) (MkQ))
(def-fns _ $ (many f : -> (many (Nat) q) (many (Nat) r))
  (match many (mk) (((Nat) q) ((Nat) r))
    ((Ph) (values (Zero)))
    ((MkQ) (values (Zero) (Zero)))))
(Zero)
; error: tests/msg_branch_values_phantom_computed_bad.sl:5:11: error: the enclosing `match` expects 2 return values, got 1: expected `(erased (Nat) q) (erased (Nat) r)`
; error: tests/msg_branch_values_phantom_computed_bad.sl:4:20: note: the return annotation of the enclosing `match` is here
