; needs: list
; expect: 1
; comptime-match verifies a Settled value and binds its fields Settled.

(let ((many two)) (Succ (Succ (Zero))))
(comptime-match many two (Succ one))
(comptime-match many one (Succ zero))

(def-lvl X)

(def-fns X $ (many use : (many (Nat) n) -> (many (Nat) m))
  (Succ zero))

(let ((many r)) (use one))
r
