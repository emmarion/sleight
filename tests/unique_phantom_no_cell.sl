; expect: 1
(def-adts $ T : -> Type enum (many Live : -> (T)) (erased Ghost : -> (T)))
(def-fns _ $ many choose : (unique (T) t) -> (many (Nat) r)
  (match unique t _
    ((Live cell) (Succ (Zero)))
    ((Ghost) (Zero))))
(def-fns _ $ erased inspect : (erased (T) t) -> (erased (Nat) r)
  (match unique t _
    ((Live cell) (Zero))
    ((Ghost) (Zero))))
(def-fns _ $ many run : -> (many (Nat) r) (choose (Live)))
run
