; error: has no Newtype open
; A Newtype parameter is no different: coercible-wrap wants it opened (DESIGN.md section 19).
; tests/newtype_of.sl is this with the open.

(def-adts $ Meters : -> Type
  enum newtype
  (many MkMeters : (many (Nat) n) -> (Meters)))
(def-lvl X)
(def-fns X $ many wrap : (erased (TyCtor -> Type) T)
    (many (ValCtor (many (Nat) n) -> (T)) C)
    (erased (Newtype C) nt)
    (many (Nat) n) -> (many (T) t)
  (coerce n (coercible-wrap C n)))
(wrap Meters MkMeters (newtype-of MkMeters) (Succ (Zero)))
