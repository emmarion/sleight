; needs: list
; expect: (Succ (Zero))

(def-lvl X)
(def-fns X $ many first : (many (Nat) a b) -> (many (Nat) r) a)
(first (Succ (Zero)) (Zero))
