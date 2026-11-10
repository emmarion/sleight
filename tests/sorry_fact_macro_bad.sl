; A fact forced from a tainted operand is not among those dispatch reads: `v` is a `(Macro)` by one alone.
(def-fns _ $ (many conv : (many (Nat) n) -> (erased Type T) (many T v))
  (values (Nat) n))
(let ((erased T) (many v)) (conv 5))
(let ((erased e)) (sorry (((Eq Type T (Macro)) q))))
(let-match erased e (Refl _ _))
(v 1 2)
; error: tests/sorry_fact_macro_bad.sl:7:2: error: `v` is one only by a fact that relies on `sorry`, so it is not dispatched as a special form or a macro
