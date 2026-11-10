; A tainted final value is not run and prints `sorry` whatever its type: a function in neither of the driver's
; forms, one in the form the driver applies to standard input, and a `Program`.
(def-lvl L)
(sorry (((Fn L (many (Nat) a) -> (many (Nat) b)) f)))
;! file "sorry/main.sl"
(def-fns _ $ (many main : (many (String) _s) -> (many (String) t))
  (sorry _))
main
;! file "sorry/program.sl"
(sorry (((Program L) p)))
; expect: sorry
; expect: sorry
; expect: sorry
; warns: tests/sorry_final.sl:4:1: warning: this unit uses `sorry` 3 times, first here; nothing that depends on it runs
