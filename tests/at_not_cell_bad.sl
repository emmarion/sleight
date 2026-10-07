(def-fns _ $ (many f : (many (Nat) h) -> (many (Nat) r))
  (at (h 1)))
; error: tests/at_not_cell_bad.sl:2:3: error: `at` wraps a `Cell` invocation or a call, and `h` : `(Nat)` is neither
