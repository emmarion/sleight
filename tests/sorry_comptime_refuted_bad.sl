; A tainted `comptime-match` is still checked as a forcing: its constructor must survive the facts in force.
(let ((many z)) (sorry (((Zero) is x))))
(comptime-match many z (Succ _p))
; error: tests/sorry_comptime_refuted_bad.sl:3:1: error: the scrutinee contradicts the facts in force
