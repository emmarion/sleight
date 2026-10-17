; expect: 8
; Refuted alternatives force different index facts before contradicting.
; None of those hypothetical facts may escape into another trial or the result.
(def-adts $ (TwoIndices : ((Nat) i j) -> Type) enum
  (many TrialZero : -> (TwoIndices (Zero) (Zero)))
  (many TrialOne : -> (TwoIndices (Succ (Zero)) (Zero)))
  (many TrialTwo : (many (Nat) x) -> (TwoIndices (Succ (Succ (Zero))) (Succ (Zero)))))
(def-fns _ $ (many trials-value : (erased (Nat) i)
    (many (TwoIndices i (Succ (Zero))) p) ->
    (many (Nat) n) (erased (Eq (Nat) i (Succ (Succ (Zero)))) index))
  (let-match many p (TrialTwo x))
  (values x (Refl (Nat) i)))
(def-fns _ $ (many trials-main : -> (many (Nat) n))
  (let ((many n) (erased _)) (trials-value (Succ (Succ (Zero))) (TrialTwo 8)))
  n)
trials-main
