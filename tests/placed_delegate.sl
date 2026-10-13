; expect: (MySucc $ MyZero)
; A `delegate` body may pass an argument through a placing, which is a renaming as a `coerce` is.
(def-adts $ (MyNat : -> Type) enum
  (many MyZero : -> (MyNat))
  (many MySucc : (many (MyNat) pred) -> (MyNat)))
(def-fns _ $ (many f : (erased (Slot) s) (erased (MyNat) v) (many (Placed s (MyNat) v) p) -> (many (MyNat) r))
  (MySucc $ unplace-at-many _ _ _ p))
(def-fns _ $ (many g at f : (many (MyNat) x) -> (many (MyNat) r))
  (delegate (f _ _ (place-at-many _ x))))
(g (MyZero))
