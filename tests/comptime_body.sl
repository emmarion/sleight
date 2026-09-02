; needs: list
; expect: (Succ (Succ (Zero)))
; comptime-match inside a function body on a top-level Const.

(let (many two) (Succ (Succ (Zero))))

(def-lvl X)
(def-fns X $ many f : (many (Nat) n) -> (many (Nat) m)
  (comptime-match two (Succ one))
  (Succ one))

(f (Zero))
