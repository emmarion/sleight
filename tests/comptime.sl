; needs: list
; expect: (Succ (Zero))
; comptime-match verifies a Const value and binds its fields Const.

(let (many two) (Succ (Succ (Zero))))
(comptime-match two (Succ one))
(comptime-match one (Succ zero))

(def-lvl X)

(def-fns X $ many use : (many (Nat) n) -> (many (Nat) m)
  (Succ zero))

(let (many r) (use one))
r
