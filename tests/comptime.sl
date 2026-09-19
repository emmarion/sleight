; needs: list
; expect: 1
; comptime-match verifies a Const value and binds its fields Const.

(let (many two) (Succ (Succ (Zero))))
(comptime-match many two (Succ one))
(comptime-match many one (Succ zero))

(def-lvl X)

(def-fns X $ many use : (many (Nat) n) -> (many (Nat) m)
  (Succ zero))

(let (many r) (use one))
r
