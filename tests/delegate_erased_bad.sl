; error: delegate in an erased position
; A delegate mark in an erased position is refused as a tail mark is there.

(def-lvl L)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(def-lvl M)
(def-fns M $ (erased g : (many (Nat) n) -> (many (Nat) m))
  (delegate (inc n)))
(Zero)
