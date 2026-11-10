; The branches of a `match` on a tainted scrutinee are a tainted scope, at `many` as at `erased`: `dump-context`
; says so, and a field bound there is tainted.
(def-fns _ $ (many f : (many (Nat) n) -> (many (Nat) r))
  (let ((many t)) (sorry (((Nat) q))))
  (match many t (((Nat) r)) ((Zero) n) ((Succ p) (dump-context p))))
; error: tainted scope: a fact that rests on `sorry` is in force
; error: p : (Nat)  [many, Hypothetical, value, tainted by `sorry`
