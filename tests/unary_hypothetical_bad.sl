; error: `unary` takes one or two constants of type `Nat` or `Char`
; A parameter is Hypothetical: unary has no value to walk.

(def-fns _ $ (erased f : (erased (Nat) n) -> (erased (Nat) r))
  (unary n)
  n)
(Zero)
