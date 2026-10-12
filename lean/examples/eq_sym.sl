(def-adts
  ((Eq : (Type A) (A x) (A y) -> Type)
    enum
    (many Refl : (erased Type A) (many A x) -> (Eq A x x))))
(def-lvl L)
(def-fns L $ (many sym : (erased Type A) (many A x) (many A y) (many (Eq A x y) e) -> (many (Eq A y x) r))
  (match many e (((Eq A y x) r))
    ((Refl a z) (Refl a z))))
(sym (Nat) (Zero) (Zero) (Refl (Nat) (Zero)))
