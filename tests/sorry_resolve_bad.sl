; A prelude macro that takes a constant by name gets no handle on a tainted one.
(let ((many a)) (sorry (((Nat) x))))
(let ((erased _p)) (prove-literal-lt a 5))
; error: tests/sorry_resolve_bad.sl:3:20: error: `prove-literal-lt` takes two constants of type `Nat` or `Char`
