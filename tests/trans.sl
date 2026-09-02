; needs: list
; expect: (Succ (Zero))
; Predates transitivity: g at L2 calls f at L0 through a proof built from two hops.

(def-lvl L0)
(def-fns L0 $ many f : (many (Nat) n) -> (many (Nat) m) (Succ n))
(def-lvl L1)
(let (erased p) (prove-predates L0 L1))
(def-lvl L2)
(let (erased q) (prove-predates L1 L2))
(def-fns L2 $ many g : (many (Nat) n) -> (many (Nat) m)
  (f (predates (predates-trans p q)) n))
(g (Zero))
