; needs: list
; expect: 1

(def-lvl L0)
(def-fns L0 $ many f : (many (Nat) n) -> (many (Nat) m) (Succ n))
(def-lvl L1)
(let (erased L0 is M) (level-of f))
(let (erased p) (prove-predates M L1))
(def-fns L1 $ many g : (many (Nat) n) -> (many (Nat) m)
  (f (predates p) n))
(g (Zero))
