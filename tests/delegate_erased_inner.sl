; expect: (Succ (Zero))
; An erased def-fns leaves nothing behind, so an erased helper inside a delegating function does
; not stand between the body and its one call (ASSUMPTIONS 77).

(def-lvl L)
(def-fns L $ many inc : (many (Nat) n) -> (many (Nat) m) (Succ n))

(def-lvl M)
(let (erased p) (prove-predates L M))

(def-fns M $ many inc-noted : (many (Nat) n) -> (many (Nat) m)
  (def-fns L $ erased same : (erased (Nat) a) -> (erased (Nat) b) a)
  (delegate (inc (predates p) n)))

(let (erased ig) (coercible-of inc-noted))
(let (many (Fn L (many (Nat) a) -> (many (Nat) b)) g) (coerce inc-noted ig))
(g (Zero))
