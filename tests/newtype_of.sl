; expect: (Succ (Zero))
; newtype-of fetches a marked type's Newtype, and a first-class coercible-wrap works through it.

(def-adts $ Meters : -> Type
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl X)
(def-fns X $ many wrap : (erased (TyCtor -> Type) T)
    (many (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Newtype T) nt)
    (many (Nat) n) -> (many (T) t)
  (coerce n (coercible-wrap C n)))

(let (many m) (wrap Meters MkMeters (newtype-of Meters) (Succ (Zero))))
(match many m (((Nat) r)) ((MkMeters n) n))
