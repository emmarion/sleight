; A tainted final value is not run and prints `sorry`: a function in the form the driver applies to standard
; input, one it applies to nothing, and a `Program`.
(def-lvl L)
(sorry (((Fn L -> (many (Nat) b)) f)))
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
