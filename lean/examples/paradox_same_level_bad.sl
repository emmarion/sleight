; tests/paradox_same_level_bad.sl in the full syntax
(def-adts
  ((Absurd : -> Type)
    enum))
(def-lvl L)
(def-adts
  ((Packed : -> Type)
    enum
    (many Pack : (many (Fn L (many (Packed) q) -> (many (Absurd) n)) f) -> (Packed))))
(def-fns L $ (many g : (many (Packed) q) -> (many (Absurd) n))
  (match many q (((Absurd) n))
    ((Pack f)
      (let ((erased p)) (prove-subterm q q))
      (f (subterm p) q))))
(g (Pack g))
