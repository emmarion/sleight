; A fact forced from a tainted operand is not among those `settled-eq` reads: `v`, a `String`, is a `(Nat)` by
; one alone, and `prove-literal-lt` does not take it for one.
(def-fns _ $ (many conv : (many (String) n) -> (erased Type T) (many T v))
  (values (String) n))
(let ((erased T) (many v)) (conv "abc"))
(let ((erased e)) (sorry (((Eq Type T (Nat)) q))))
(let-match erased e (Refl _ _))
(let ((erased _p)) (prove-literal-lt v 5))
; error: tests/sorry_fact_literal_bad.sl:8:20: error: `prove-literal-lt` takes two constants of type `Nat` or `Char`
