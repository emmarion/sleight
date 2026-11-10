; A form whose results are all tainted leaves no code, and the arguments hoisted out of it (DESIGN.md section 15)
; go with it: the same-level call in an argument of a tainted call is not in the code that the tail-position
; check reads, so it draws no warning. So it is with a `let-match` on a tainted scrutinee.
(def-fns _ $ (many count : (subterm many (Nat) n) -> (many (Nat) r))
  (let-match many n (Succ p) ((Zero) 0))
  (let ((many k)) (sorry (((Nat) y))))
  (Succ $ nat-add k $ count p))
(def-fns _ $ (many first : (subterm many (Nat) n) -> (many (Nat) r))
  (let-match many n (Succ p) ((Zero) 0))
  (let ((many k)) (sorry (((Nat) y))))
  (let-match many (MkPair _ _ (first p) k) (MkPair _ _ a _b))
  a)
(count 2)
;! file "sorry/first.sl"
(first 2)
; expect: sorry
; expect: sorry
; warns: tests/sorry_hoisted.sl:6:19: warning: this unit uses `sorry` 2 times, first here; nothing that depends on it runs
