; expect: 1
; Erased definitions leave nothing behind, so neither an erased def-fns nor a def-adts declaring
; only phantom constructors stands between a delegating body and its one call (ASSUMPTIONS 77).
; The proof is then fetched through an alias of the function's name (section 8).

(def-lvl L)
(def-fns L $ (many inc : (many (Nat) n) -> (many (Nat) m)) (Succ n))

(def-lvl M)
(let ((erased p)) (prove-predates L M))

(def-fns M $ (many inc-noted at inc : (many (Nat) n) -> (many (Nat) m))
  (def-fns L $ (erased _same : (erased (Nat) a) -> (erased (Nat) b)) a)
  (def-adts $ (Tally : -> Type)
    enum
    (erased Mark : (erased (Nat) k) -> (Tally)))
  (delegate (inc (predates p) n)))

(let ((many noted)) inc-noted)
(let ((erased ig)) (coercible-of (delegate-of noted)))
(let ((many (Fn L (many (Nat) a) -> (many (Nat) b)) g)) (coerce noted ig))
(g (Zero))
; warns: tests/delegate_erased_inner.sl:17:18: warning: unnecessary `(predates _)`; drop it
