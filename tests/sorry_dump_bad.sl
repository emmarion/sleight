; `dump-context` reads a stored value against the facts the elaborator reads, not a fact forced from a tainted
; operand: `w`, a list, is not shown as the `String` that such a fact makes its type.
(def-fns _ $ (many conv : (erased Type A) (many A a) -> (erased Type T) (many T v))
  (values A a))
(let ((erased K) (many w)) (conv (List (Nat)) (Cons _ 1 (Nil _))))
(let ((erased e)) (sorry (((Eq Type K (String)) q))))
(let-match erased e (Refl _ _))
(dump-context w)
; error: tests/sorry_dump_bad.sl:8:1: error: `dump-context` stops elaboration here and reports what the checker knows
; error: w : (String)  [many, Settled, value, bound at tests/sorry_dump_bad.sl:5:18]
