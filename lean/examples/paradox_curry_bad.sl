; tests/paradox_curry_bad.sl in the full syntax
(def-adts
  ((Absurd : -> Type)
    enum))
(def-adts
  ((Bad : -> Type)
    enum
    (many MkBad : (erased (Level) l) (many (Fn l (many (Bad) b) -> (many (Absurd) f)) g) -> (Bad))))
(def-lvl W)
(def-fns W $ (many omega : (many (Bad) b) -> (many (Absurd) f))
  (match many b (((Absurd) f))
    ((MkBad l g)
      (let ((erased p)) (prove-predates l W))
      (g (predates p) b))))
(omega (MkBad W omega))
