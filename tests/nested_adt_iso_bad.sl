; error: branch `Refl` is not refuted
; Two def-adts in one body with identical declarations, each capturing the parameter A: nothing refutes
; equating them, so the absurd branch is an error.

(def-lvl X)
(def-fns X $ (many outer : (erased Type A) -> (many (Nat) n))
  (def-adts $ (Bx : -> Type) enum (many K1 : (many A v) -> (Bx)))
  (def-adts $ (By : -> Type) enum (many K2 : (many A v) -> (By)))
  (def-fns X $ (many absurd inner : (erased (Eq Type (Bx) (By)) p) -> (many (Nat) m))
    (match erased p _ (absurd Refl)))
  (Zero))
(outer (Nat))
