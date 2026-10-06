(def-fns _ $ (many g : (erased (Level) M) (many (Fn M (many (Nat) x) -> (many (Nat) y)) h) (many (Nat) n) -> (many (Nat) y))
  (h n n))
; error: tests/arity_param_bad.sl:2:3: error: `h` expects 1 argument, got 2: expected `(many (Nat) x)`
; error: tests/arity_param_bad.sl:1:43: note: function `h` is declared here
