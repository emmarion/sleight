; needs: ../std/macro
; error: tests/macro_frame_arg_bad.sl:5:10: error: type mismatch: expected `(Bool)`, got `(Nat)`
; error: tests/macro_frame_arg_bad.sl:5:3: note: in the expansion of `and` here
(def-fns _ $ (many h : (many (Bool) x) -> (many (Bool) m))
  (and x (Zero)))
