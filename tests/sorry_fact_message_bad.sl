; A fact forced from a tainted operand is not among those a message is read against: `v` is a `(String)` by one alone.
(def-fns _ $ (many conv : (many (Nat) n) -> (erased Type T) (many T v))
  (values (Nat) n))
(let ((erased T) (many v)) (conv 5))
(let ((erased e)) (sorry (((Eq Type T (String)) q))))
(let-match erased e (Refl _ _))
(compile-warn v)
; error: tests/sorry_fact_message_bad.sl:7:15: error: the message of `compile-warn` must be a `Settled`, non-erased `String`; `v` is one only by a fact that relies on `sorry`
