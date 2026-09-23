; error: `notail` in an erased position
; A notail mark in an erased position is refused as tail and delegate are.

(def-fns _ $ (erased count : (subterm many (List (Nat)) xs) -> (many (Nat) n))
  (match erased xs _
    ((Nil _) (Zero))
    ((Cons _ _ rest) (Succ $ notail $ count rest))))
(Zero)
