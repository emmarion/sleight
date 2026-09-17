; expect: 1
; Erased definitions leave nothing behind, so neither an erased def-fns nor a def-adts declaring
; only phantom constructors stands between a delegating body and its one call (ASSUMPTIONS 77).
; The proof is then fetched through an alias of the function's name (ASSUMPTIONS 78).

(def-lvl L)
(def-fns L $ many inc : (many (Nat) n) -> (many (Nat) m) (Succ n))

(def-lvl M)
(let (erased p) (prove-predates L M))

(def-fns M $ many inc-noted : (many (Nat) n) -> (many (Nat) m)
  (def-fns L $ erased same : (erased (Nat) a) -> (erased (Nat) b) a)
  (def-adts $ Tally : -> Type
    enum
    (erased Mark : (erased (Nat) k) -> (Tally)))
  (delegate (inc (predates p) n)))

(let (many noted) inc-noted)
(let (erased ig) (coercible-of noted))
(let (many (Fn L (many (Nat) a) -> (many (Nat) b)) g) (coerce noted ig))
(g (Zero))
