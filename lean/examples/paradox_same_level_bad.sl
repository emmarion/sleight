; tests/paradox_same_level_bad.sl in the minimal syntax, the level carried as an index
(def-adts (Absurd ()))
(def-adts (Packed (((Level) l)) (Pack (((Level) l) ((Fn l (((Packed l) q)) (((Absurd) n))) f)) (Packed l))))
(def-lvl L)
(def-fns L (g (((Packed L) q)) (((Absurd) n))
  (match q (((Absurd) n))
    ((Pack l f) (let (p) (prove-subterm q q)) (f (subterm p) q)))))
(g (Pack L g))
