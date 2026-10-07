; expect: 7
; A return written `at` an earlier return (section 36): the caller's `let` reconstructs it from the
; word it just bound.
(def-fns _ $ (many twin : (many (Nat) x) -> (many (Nat) a) (many (Nat) r at a))
  (let ((many b)) (Succ x))
  (values b b))
(let ((many p) (many q)) (twin 6))
q
