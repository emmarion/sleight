; `native-compute` is tainted by any of its functions: with a tainted one among them nothing is compiled or
; run, and every result is tainted, that of an untainted function included.
; host-path: yes
(def-fns _ $ (many junk : -> (many (Bool) m)) (sorry _))
(def-fns _ $ (many good : -> (many (Bool) m)) (BTrue))
(let ((many a) (many _b)) (native-compute good junk))
(let ((many c)) (native-compute good))
c
;! file "sorry/native-tainted.sl"
a
; expect: (BTrue)
; expect: sorry
; warns: tests/sorry_native.sl:4:47: warning: this unit uses `sorry` once, here; nothing that depends on it runs
