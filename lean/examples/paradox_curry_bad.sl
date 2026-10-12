; tests/paradox_curry_bad.sl in the minimal syntax
(def-adts (Absurd ()))
(def-adts (Bad () (MkBad (((Level) l) ((Fn l (((Bad) b)) (((Absurd) f))) g)) (Bad))))
(def-lvl W)
(def-fns W (omega (((Bad) b)) (((Absurd) f))
  (match b (((Absurd) f))
    ((MkBad l g) (let (p) (prove-predates l W)) (g (predates p) b)))))
(omega (MkBad W omega))
