; A `sorry` can refute: an absurd function or an absurd-by-proof branch whose refutation rests on one is
; tainted, and so is what calls it or the match holding it. `boom` and `pred` would reach `absurd` code on `0`.
(def-fns _ $ (many absurd boom : (many (Nat) _n) -> (many (Nat) m))
  (sorry (((False) f))))
(def-fns _ $ (many safe : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) m))
    ((Zero) (boom n))
    ((Succ p) p)))
(def-fns _ $ (many pred : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) m))
    (absurd (Zero) (sorry (((False) f))))
    ((Succ p) p)))
(safe 0)
;! file "sorry/pred.sl"
(pred 0)
; expect: sorry
; expect: sorry
; warns: tests/sorry_absurd.sl:4:3: warning: this unit uses `sorry` 2 times, first here; nothing that depends on it runs
