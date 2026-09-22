; expect: 1
(def-adts $ (Box : -> Type)
  enum newtype
  (many Boxed : (unique (Nat) n) -> (Box)))
(let ((unique box)) (Boxed (Succ (Zero))))
(comptime-match unique box (Boxed n))
(share n)
