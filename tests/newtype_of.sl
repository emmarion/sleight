; expect: 1
; newtype-of fetches the Newtype naming a marked type's wrapping constructor, and a first-class coercible-wrap
; works through it once it is opened (DESIGN.md section 19).

(def-adts $ Meters : -> Type
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl X)
(def-fns X $ many wrap : (erased (TyCtor -> Type) T)
    (many (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Newtype C) nt)
    (many (Nat) n) -> (many (T) t)
  (open-adt erased nt)
  (coerce n (coercible-wrap C n)))

(let (many m) (wrap Meters MkMeters (newtype-of MkMeters) (Succ (Zero))))
(match many m (((Nat) r)) ((MkMeters n) n))
