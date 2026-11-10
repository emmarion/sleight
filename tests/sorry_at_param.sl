; A parameter written `at` a tainted entry is read from that entry, as it would be from a value; the function
; is tainted by its signature.
(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))
(let ((many x)) (inc 4))
(let ((many t)) (sorry (((Nat) q at x))))
(def-fns _ $ (many f : (many (Nat) a at t) -> (many (Nat) r))
  (Succ a))
(inc x)
;! file "sorry/at-param.sl"
(f x)
; expect: 6
; expect: sorry
; warns: tests/sorry_at_param.sl:6:17: warning: this unit uses `sorry` once, here; nothing that depends on it runs
