; needs: list
; expect: 1

(def-lvl X)

(def-fns X $ (many swap : (many (Nat) a) (many (Nat) b) -> (many (Nat) c) (many (Nat) d))
  (values b a))

(def-lvl Y)
(let ((erased p)) (prove-predates X Y))

(def-fns Y $ (many second : (many (Nat) a) (many (Nat) b) -> (many (Nat) d))
  (let ((many _) (many d)) (swap (predates p) a b))
  d)

(second (Succ (Zero)) (Zero))
; warns: tests/multi.sl:13:34: warning: unnecessary `(predates _)`; drop it
