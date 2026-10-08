; Two identical Matchables for an empty type, one a parameter opened beside False's own, merge into one record
; (DESIGN.md section 8) and still make the type empty (section 8).

(def-lvl X)
(def-fns X $ (many absurd boom : (erased (Matchable enum False) m) (many (False) f) -> (many (Nat) n))
  (open-adt erased m)
  f)
