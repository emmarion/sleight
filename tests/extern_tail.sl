; expect: (Zero)
; A tail-marked loop counting a Nat down a million times, the count computed at runtime so nothing is
; embedded: the extracted program runs it through the extern match in constant stack, which holds only
; if the FFI's match keeps a branch body in tail position (ASSUMPTIONS 133).

(def-fns _ $ many flip : (many (Nat) a) -> (many (Nat) b)
  (match many a _ ((Zero) (Succ (Zero))) ((Succ k) (Zero))))

(def-lvl X)
(def-fns X $ many count-down : (subterm many (Nat) n) (many (Nat) parity) -> (many (Nat) r)
  (match many n _
    ((Zero) parity)
    ((Succ k) (tail (count-down (subterm (prove-subterm k n)) k (flip parity))))))

(def-lvl Y)
(let (erased xy) (prove-predates X Y))
(def-fns Y $ many run : -> (many (Nat) r)
  (let (many n) (nat-mul 1000 1000))
  (count-down (predates xy) n (Zero)))

run
