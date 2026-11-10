; A form whose results are all tainted compiles to the erased token, but what was hoisted out of it before it
; (DESIGN.md section 15) stays, so the unmarked same-level call in an argument still warns; so does a
; `let-match` on a tainted scrutinee, whose own code is dropped.
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
; warns: tests/sorry_hoisted.sl:7:21: warning: same-level call to `count` is unmarked; mark it `notail`
; warns: tests/sorry_hoisted.sl:11:31: warning: same-level call to `first` is unmarked; mark it `notail`
; warns: tests/sorry_hoisted.sl:6:19: warning: this unit uses `sorry` 2 times, first here; nothing that depends on it runs
