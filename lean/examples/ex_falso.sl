(def-adts
  ((False : -> Type)
    enum))
(def-adts
  ((Eq : (Type A) (A x) (A y) -> Type)
    enum
    (many Refl : (erased Type A) (many A x) -> (Eq A x x))))
(def-lvl L)
(def-fns L $ (many explode : (many (False) f) -> (many (Nat) n))
  (match many f (((Nat) n))))
(def-fns L $ (many zero-not-one : (many (Eq (Nat) (Zero) (Succ (Zero))) e) -> (many (False) f))
  (match many e (((False) f))))
(Zero)
