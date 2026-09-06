; error: takes a (subterm p) annotation, not (predates p)
; A same-level call carrying a Predates annotation is refused as such: the kind is read from the levels.

(def-lvl P)
(def-lvl Q)
(let (erased pq) (prove-predates P Q))
(def-fns Q $ many f : (subterm many (Nat) n) -> (many (Nat) m)
  (match many n _
    ((Zero) (Zero))
    ((Succ k) (f (predates pq) k))))
