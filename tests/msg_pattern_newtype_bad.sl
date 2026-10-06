(def-fns _ $ (many f : (many (MaybeUninit (Nat)) m) -> (many (Nat) r))
  (match many m _
    ((Init a) (Zero))
    ((Uninit a s) (Zero))))
(Zero)
; error: tests/msg_pattern_newtype_bad.sl:3:6: error: a `match` branch on `Init` under `many` expects 2 binders, got 1: expected `(erased Type A) (many A value)`
; error: lib/prelude.sl:<**>: note: value constructor `Init` is declared here
