; A call is tainted by any of its operands, an erased argument included, and by a tainted function. A function
; is tainted when a result of its body is; one whose body only binds a tainted value it never uses is not.
(def-fns _ $ (many inc : (many (Nat) n) (erased (Nat) _k) -> (many (Nat) m))
  (Succ n))
(def-fns _ $ (many unused : (many (Nat) n) -> (many (Nat) m))
  (let ((many _x)) (inc (sorry (((Nat) y))) n))
  (Succ n))
(def-fns _ $ (many partial : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) m))
    ((Zero) (sorry _))
    ((Succ p) p)))
(MkPair (Nat) (Nat) (inc 4 0) (unused 1))
;! file "sorry/erased-arg.sl"
(inc 4 (sorry _))
;! file "sorry/arg.sl"
(inc (sorry _) 0)
;! file "sorry/function.sl"
(partial 3)
; expect: (MkPair _ _ 5 2)
; expect: sorry
; expect: sorry
; expect: sorry
; warns: tests/sorry_calls.sl:6:25: warning: this unit uses `sorry` 4 times, first here; nothing that depends on it runs
