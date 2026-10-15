; expect: 0
; Two def-adts in one body capturing the parameter A, with different numbers of constructors: their
; Matchables cannot be unified, so equating the types is refuted.

(def-lvl X)
(def-fns X $ (many outer : (erased Type A) -> (many (Nat) n))
  (def-adts $ (Bx : -> Type) enum (many K1 : (many A v) -> (Bx)))
  (def-adts $ (By : -> Type) enum (many K2 : (many A v) -> (By)) (many K3 : (many A v) -> (By)))
  (def-fns X $ (many absurd inner : (erased (Eq Type (Bx) (By)) p) -> (many (Nat) m))
    (match erased p _ (absurd Refl)))
  (Zero))
(outer (Nat))
