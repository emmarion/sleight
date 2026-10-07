; expect: 2
; The `else` of a match at `many` may bind the scrutinee back, `is` and at it (section 37).
(def-adts $ (D : -> Type) enum (many A : -> (D)) (many B : (many (Nat) n) -> (D)))
(def-fns _ $ (many same : (many (D) x) -> (many x is r at x))
  (match many x _ ((A u) (at (u))) (else y y)))
(let ((many x)) (same (B 2)))
(match many x (((Nat) n)) (absurd A) ((B n) n))
