; A `sorry` can refute: an absurd function or an absurd-by-proof branch whose refutation rests on one is
; tainted, and so is what calls it, the match holding it, and what follows a `let-match` holding it. Each of
; these would reach `absurd` code, or a match with no branch for its value, if it ran.
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
(def-fns _ $ (many pred-let : (many (Nat) n) -> (many (Nat) m))
  (let-match many n (Succ p) (absurd (Zero) (sorry (((False) f)))))
  p)
(def-fns _ $ (many pred-nested : (many (Nat) n) -> (many (Nat) m))
  (match many n (((Nat) m))
    (absurd (Zero) (match erased n _ (absurd (Zero) (sorry (((False) f)))) (absurd Succ)))
    ((Succ p) p)))
(def-fns _ $ (many absurd never : (many (Nat) n) -> (many (Nat) m))
  (match erased n _
    (absurd (Zero) (sorry (((False) f))))
    (absurd (Succ _p) (sorry (((False) f))))))
(safe 0)
;! file "sorry/pred.sl"
(pred 0)
;! file "sorry/pred-let.sl"
(pred-let 0)
;! file "sorry/pred-nested.sl"
(def-fns _ $ (many main : -> (many (Nat) m))
  (pred-nested 0))
main
;! file "sorry/never.sl"
(never 3)
; expect: sorry
; expect: sorry
; expect: sorry
; expect: sorry
; expect: sorry
; warns: tests/sorry_absurd.sl:5:3: warning: this unit uses `sorry` 6 times, first here; nothing that depends on it runs
