; needs: ../mini/base ../mini/term
; expect: (Cons _ (TFn (Bound 0) (Cons _ (MkEntry (BFalse) (BFalse) $ TyApp (Ref 3) (Cons _ (MkEntry (BFalse) (BFalse) $ TUniv) $ Nil _) $ Cons _ (Bound 0) $ Nil _) $ Nil _) $ Cons _ (MkEntry (BFalse) (BTrue) $ ValApp (Bound 0) (Cons _ (MkEntry (BFalse) (BFalse) $ TUniv) $ Nil _) (Bound 0) $ Cons _ (Bound 1) $ Nil _) $ Nil _) $ Cons _ (TFn (Ref 7) (Cons _ (MkEntry (BFalse) (BFalse) $ TyApp (Ref 3) (Cons _ (MkEntry (BFalse) (BFalse) $ TUniv) $ Nil _) $ Cons _ (Ref 7) $ Nil _) $ Nil _) $ Cons _ (MkEntry (BFalse) (BTrue) $ ValApp (Bound 0) (Cons _ (MkEntry (BFalse) (BFalse) $ TUniv) $ Nil _) (Bound 0) $ Cons _ (Ref 7) $ Nil _) $ Nil _) $ Nil _)
; The term layer of mini/: a binder substituted through a function type, where the return entry sits one
; binder deeper than the level and the parameter; the abstraction back and the assignability decision are
; exercised by the checks below, each expected to come out as noted.

(let ((many z)) (Zero))
(let ((many one)) (Succ z))
(let ((many subs)) (Cons _ (Some _ (Ref 7)) (Nil _)))
(let ((many ps)) (Cons _ (MkEntry (BFalse) (BFalse) (TUniv)) (Nil _)))
(let ((many t)) (TFn (Bound z) (Cons _ (MkEntry (BFalse) (BFalse) (TyApp (Ref 3) ps (Cons _ (Bound z) (Nil _)))) (Nil _)) (Cons _ (MkEntry (BFalse) (BTrue) (ValApp (Bound z) ps (Bound z) (Cons _ (Bound one) (Nil _)))) (Nil _))))

(let ((many s) (erased sp))
  (subst subs (Succ (Zero)) (LengthCons _ _ _ _ (LengthNil _)) t
    (ClFn (Succ (Zero)) _ _ _ (Succ (Succ (Zero))) (Succ (Succ (Succ (Zero)))) (ClBound (Succ (Zero)) (Zero) (LtZ (Zero)))
      (ClTCons (Succ (Zero)) _ _ _ _ (Succ (Succ (Zero))) (ClTyApp (Succ (Zero)) _ _ _ _ (ClRef (Succ (Zero)) 3) (ClTCons (Succ (Zero)) _ _ _ _ (Succ (Succ (Zero))) (ClUniv (Succ (Zero))) (ClTNil (Succ (Succ (Zero))))) (ClCons (Succ (Zero)) _ _ (ClBound (Succ (Zero)) (Zero) (LtZ (Zero))) (ClNil (Succ (Zero))))) (ClTNil (Succ (Succ (Zero)))))
      (ClTCons (Succ (Succ (Zero))) _ _ _ _ (Succ (Succ (Succ (Zero))))
        (ClValApp (Succ (Succ (Zero))) _ _ _ _ _ (ClBound (Succ (Succ (Zero))) (Zero) (LtZ (Succ (Zero)))) (ClTCons (Succ (Succ (Zero))) _ _ _ _ (Succ (Succ (Succ (Zero)))) (ClUniv (Succ (Succ (Zero)))) (ClTNil (Succ (Succ (Succ (Zero))))))
          (ClBound (Succ (Succ (Succ (Zero)))) (Zero) (LtZ (Succ (Succ (Zero))))) (ClCons (Succ (Succ (Zero))) _ _ (ClBound (Succ (Succ (Zero))) (Succ (Zero)) (LtS (Zero) (Succ (Zero)) (LtZ (Zero)))) (ClNil (Succ (Succ (Zero))))))
        (ClTNil (Succ (Succ (Succ (Zero)))))))))

; Abstracting 7 out of the substituted term gives the original back, the two printed together.
(let ((many u) (erased ap)) (abstract (Cons _ (Some _ 7) (Nil _)) s))

; 7 occurs in the substituted term, so it cannot be assigned; 9 may be, its only binder being the return's own.
(let ((many no7)) (match many (assign-dec 0 7 s) (((Bool) r)) ((ADNo c d e q) (BTrue)) ((ADYes c d e q) (BFalse))))
(comptime-match many no7 (BTrue))
(let ((many yes9)) (match many (assign-dec 0 9 s) (((Bool) r)) ((ADNo c d e q) (BFalse)) ((ADYes c d e q) (BTrue))))
(comptime-match many yes9 (BTrue))
(Cons _ u $ Cons _ s $ Nil _)
