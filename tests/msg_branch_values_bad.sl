(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) q) (many (Nat) r))
  (match many x (((Nat) q) ((Nat) r))
    ((Zero) (values x))
    ((Succ p) (values p p))))
; error: tests/msg_branch_values_bad.sl:3:13: error: the enclosing `match` expects 2 return values, got 1: expected `(many (Nat) q) (many (Nat) r)`
; error: tests/msg_branch_values_bad.sl:2:17: note: the return annotation of the enclosing `match` is here
