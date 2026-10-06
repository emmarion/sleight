(def-fns _ $ (many id : (many (Nat) v) -> (many (Nat) w)) v)
(def-fns _ $ (many f : (many (Nat) x) -> (many (Nat) q) (many (Nat) r))
  (match many (id x) (((Nat) q) ((Nat) r))
    ((Zero) (values x))
    ((Succ p) (values p p))))
; error: tests/msg_branch_values_computed_bad.sl:4:13: error: the enclosing `match` expects 2 return values, got 1: expected `(many (Nat) q) (many (Nat) r)`
; error: tests/msg_branch_values_computed_bad.sl:3:22: note: the return annotation of the enclosing `match` is here
