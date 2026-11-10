; A fact forced from a tainted operand is not among those dispatch reads: `v` is a `(Special)` by one alone,
; whether its form stands as a statement or as the final expression.
(def-fns _ $ (many conv : (many (Nat) n) -> (erased Type T) (many T v))
  (values (Nat) n))
(let ((erased T) (many v)) (conv 5))
(let ((erased e)) (sorry (((Eq Type T (Special)) q))))
(let-match erased e (Refl _ _))
(v ((many x)) 3)
x
; error: tests/sorry_fact_special_bad.sl:8:2: error: `v` is one only by a fact that relies on `sorry`, so it is not dispatched as a special form or a macro
