(def-fns _ $ (many k : (many (ValCtor (many (Nat) pred) -> (Nat)) c) -> (many (Nat) y))
  (c (Zero) (Zero)))
; error: tests/msg_arity_valctor_param_bad.sl:2:3: error: `c` expects 1 argument, got 2: expected `(many (Nat) pred)`
; error: tests/msg_arity_valctor_param_bad.sl:1:24: note: value constructor `c` is declared here
