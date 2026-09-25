; error: is not refuted: it may be headed by
(def-adts $ (Opt : -> Type) enum
  (many Full : (many (Nat) v) -> (Opt))
  (many Empty : -> (Opt)))
(def-lvl X)
(def-adts $ (Surely : -> Type) enum
  (many Got : (many (Nat) v) -> (Surely))
  (many Nope : (erased (Nat) f) -> (Surely)))
(def-fns X $ (many mk : (many (Nat) n) -> (many (Surely) s)) (Got n))
(let ((many y)) (mk 7))
(let-match many y (Got seven) (absurd (Nope f) f))
seven
