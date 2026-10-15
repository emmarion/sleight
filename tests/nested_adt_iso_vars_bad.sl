; error: branch `Refl` is not refuted
; As nested_adt_iso_bad, but the two declarations capture different parameters: equating them would
; equate A and C, which refutes nothing.

(def-lvl X)
(def-fns X $ (many outer : (erased Type A) (erased Type C) -> (many (Nat) n))
  (def-adts $ (Bx : -> Type) enum (many K1 : (many A v) -> (Bx)))
  (def-adts $ (By : -> Type) enum (many K2 : (many C v) -> (By)))
  (def-fns X $ (many absurd inner : (erased (Eq Type (Bx) (By)) p) -> (many (Nat) m))
    (match erased p _ (absurd Refl)))
  (Zero))
(outer (Nat) (Nat))
