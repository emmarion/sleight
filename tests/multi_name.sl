; needs: list
; expect: 1

(def-lvl X)
(def-fns X $ many first : (many (Nat) a b) -> (many (Nat) r) a)
(first (Succ (Zero)) (Zero))
