; error: `MkW` has a field written `at`, so `W` cannot be marked `newtype`
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (unique (MyNat) pred) -> (MyNat)))
(def-adts $ (W : ((Slot) s) -> Type) enum newtype
  (many MkW : (many (Slot) s) (unique (MyNat) v at s) -> (W s)))
