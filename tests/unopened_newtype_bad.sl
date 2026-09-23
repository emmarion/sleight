; error: has no opened newtype `Matchable`

(def-adts $ (Meters : -> Type)
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))
(def-lvl X)
(def-fns X $ (many wrap : (erased (TyCtor -> Type) T)
    (many (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Matchable enum newtype T (many C)) nt)
    (many (Nat) n) -> (many (T) t))
  (coerce n (coercible-wrap (Shared) C n)))
(wrap Meters MkMeters (matchable-of Meters) (Succ (Zero)))
