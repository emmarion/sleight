; A `comptime-match` on a tainted scrutinee checks nothing against a value: `a` would be `(Succ ...)` if it
; were computed. What follows it is tainted, to the end of the unit.
(let ((many a)) (sorry (((Nat) x))))
(comptime-match many a (Zero))
(let ((many b)) 5)
(MkPair (Nat) (Nat) b b)
; expect: sorry
; warns: tests/sorry_comptime.sl:3:17: warning: this unit uses `sorry` once, here; nothing that depends on it runs
