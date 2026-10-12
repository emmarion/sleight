(def-adts
  ((Vec : (Type A) ((Nat) n) -> Type)
    enum
    (many VNil : (erased Type A) -> (Vec A (Zero)))
    (many VCons : (erased Type A) (many (Nat) n) (many A x) (many (Vec A n) xs) -> (Vec A (Succ n)))))
(def-lvl L)
(def-fns L $ (many head : (erased Type A) (many (Nat) n) (many (Vec A (Succ n)) v) -> (many A x))
  (match many v ((A x))
    ((VNil a) (head A n v))
    ((VCons a m x xs) x)))
(Zero)
