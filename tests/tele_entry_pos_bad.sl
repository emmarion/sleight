(def-fns _ $ (many f : -> (many (Nat) r))
  (let ((many y) (Succ (Zero))))
  (Zero))
; error: tests/tele_entry_pos_bad.sl:2:18: error: malformed telescope entry `(Succ (Zero))`
