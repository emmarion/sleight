(def-fns _ $ (many f : (many (Sharing) s) -> (many (Nat) r))
  (match many s _
    ((Unique) (Zero))))
(Zero)
; error: tests/msg_missing_builtin_bad.sl:2:3: error: this `match` is missing a branch for the following unrefuted constructor:
; error: tests/msg_missing_builtin_bad.sl:2:3: note: value constructor `Shared`, which is built in
