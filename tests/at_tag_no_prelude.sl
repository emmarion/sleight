; prelude: none
; expect: (Right _)
(def-adts $ (Coin : -> Type) enum
  (many Heads : -> (Coin))
  (many Tails : -> (Coin)))

(def-adts $ (Side : -> Type) enum
  (many Left : -> (Side))
  (many Right : (erased (Coin) k) -> (Side)))

(def-fns _ $ (many at coin-side : (many (Coin) c) -> (many (Side) s at c))
  (match many c (at (((Side) s at c)))
    ((Heads) (slot-tag c) (Left))
    ((Tails) (slot-tag c) (Right c))))

(coin-side (Tails))
