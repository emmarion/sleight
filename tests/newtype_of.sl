; expect: 1

(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))

(def-lvl X)
(def-fns X $ (many wrap : (erased (TyCtor -> Type) T)
    (erased (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Matchable enum newtype T (many C)) nt)
    (many (Nat) n) -> (many (T) t))
  (open-adt erased nt)
  (coerce n (coercible-wrap (Shared) C n)))

(let ((many m)) (wrap Meters MkMeters (matchable-of Meters) (Succ (Zero))))
(match many m (((Nat) r)) ((MkMeters n) n))
