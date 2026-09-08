; expect: <function boom>
; Two identical Matchables for an empty type, one a parameter opened beside False's own, merge into one record
; (proposals/matchable-newtype-opening.md) and still make the type empty (section 19).

(def-lvl X)
(def-fns X $ many absurd boom : (erased (Matchable enum False) m) (many (False) f) -> (many (Nat) n)
  (open-adt erased m)
  f)
boom
