; tests/paradox_same_level_bad.sl in the minimal syntax
(def-adts (Absurd ()))
(def-lvl L)
(def-adts (Packed () (Pack (((Fn L (((Packed) q)) (((Absurd) n))) f)) (Packed))))
(def-fns L (g (((Packed) q)) (((Absurd) n))
  (match q (((Absurd) n))
    ((Pack f) (let (p) (prove-subterm q q)) (f (subterm p) q)))))
(g (Pack g))
