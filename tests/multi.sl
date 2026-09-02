; needs: list
; expect: (Succ (Zero))

(def-lvl X)

(def-fns X $ many swap : (many (Nat) a) (many (Nat) b) -> (many (Nat) c) (many (Nat) d)
  (values b a))

(def-lvl Y)
(let (erased p) (prove-predates X Y))

(def-fns Y $ many second : (many (Nat) a) (many (Nat) b) -> (many (Nat) d)
  (let (many c) (many d) (swap (predates p) a b))
  d)

(second (Succ (Zero)) (Zero))
