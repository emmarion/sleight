; expect: (Cons _ (Left) $ Cons _ (Right _) $ Nil _)
(def-adts $ (Coin : -> Type) enum
  (many Heads : -> (Coin))
  (many Tails : -> (Coin)))

(def-adts $ (Side : -> Type) enum
  (many Left : -> (Side))
  (many Mid : (many (Coin) c) -> (Side))
  (many Right : (erased (Coin) k) -> (Side)))

(def-fns _ $ (many at coin-side : (many (Coin) c) -> (many (Side) s at c))
  (match many c (at (((Side) s at c)))
    ((Heads) (slot-tag c) (Left))
    ((Tails) (slot-tag c) (Right c))))

(Cons _ (coin-side (Heads)) $ Cons _ (coin-side (Tails)) $ Nil _)
