; expect: _
; Two identical Matchables for an empty type, one a parameter opened beside False's own, merge into one record
; (DESIGN.md section 19) and still make the type empty (section 19).

(def-lvl X)
(def-fns X $ (many absurd boom : (erased (Matchable enum False) m) (many (False) f) -> (many (Nat) n))
  (open-adt erased m)
  f)
boom
