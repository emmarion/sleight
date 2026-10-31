; error: return does not satisfy `at` `(slot-of c)`
(def-adts $ (Coin : -> Type) enum
  (many Heads : -> (Coin))
  (many Tails : -> (Coin)))

(def-fns _ $ (many at coin-coin : (many (Coin) c) -> (many (Coin) d at c))
  (match many c (at (((Coin) d at c)))
    ((Heads) (Heads))
    ((Tails) (Tails))))
(Zero)
