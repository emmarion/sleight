; expect: <function boom>
; Two identical Matchables for an empty type in scope, one a parameter, still make it empty (section 19).

(def-lvl X)
(def-fns X $ many absurd boom : (erased (Matchable enum False) m) (many (False) f) -> (many (Nat) n)
  f)
boom
