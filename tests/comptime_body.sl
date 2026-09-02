; needs: list
; error: run-position statement
; comptime-match is confined to run position (section 15): inside a function body it is an error.

(let (many two) (Succ (Succ (Zero))))

(def-lvl X)
(def-fns X $ many f : (many (Nat) n) -> (many (Nat) m)
  (comptime-match two (Succ one))
  (Succ one))
