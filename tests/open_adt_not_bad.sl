; error: is not a Matchable or a Newtype
; open-adt names a Matchable or a Newtype and nothing else.

(def-lvl X)
(def-fns X $ many f : (many (Nat) n) -> (many (Nat) r)
  (open-adt many n)
  n)
f
