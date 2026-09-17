; needs: ../mini/base ../mini/term
; expect: (Cons (Fn (Bound (Zero)) (Cons ((BFalse) (BFalse) (App (Ref (Succ (Succ (Succ (Zero))))) (Cons (Bound (Zero)) (Nil)))) (Nil)) (Cons ((BFalse) (BTrue) (App (Bound (Zero)) (Cons (Bound (Succ (Zero))) (Nil)))) (Nil))) (Cons (Fn (Ref (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))) (Cons ((BFalse) (BFalse) (App (Ref (Succ (Succ (Succ (Zero))))) (Cons (Ref (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))) (Nil)))) (Nil)) (Cons ((BFalse) (BTrue) (App (Bound (Zero)) (Cons (Ref (Succ (Succ (Succ (Succ (Succ (Succ (Succ (Zero))))))))) (Nil)))) (Nil))) (Nil)))
; The term layer of mini/: a binder substituted through a function type, where the return entry sits one
; binder deeper than the level and the parameter; the abstraction back and the assignability decision are
; exercised by the checks below, each expected to come out as noted.

(let (many z) (Zero))
(let (many one) (Succ z))
(let (many sub) (Cons _ (Some _ (Ref 7)) (Nil _)))
(let (many t) (Fn (Bound z) (Cons _ (MkEntry (BFalse) (BFalse) (App (Ref 3) (Cons _ (Bound z) (Nil _)))) (Nil _)) (Cons _ (MkEntry (BFalse) (BTrue) (App (Bound z) (Cons _ (Bound one) (Nil _)))) (Nil _))))

(let (many s) (erased sp)
  (subst sub (Succ (Zero)) (LenCons _ _ _ _ (LenNil _)) t
    (ClFn (Succ (Zero)) _ _ _ (Succ (Succ (Zero))) (Succ (Succ (Succ (Zero)))) (ClBound (Succ (Zero)) (Zero) (LtZ (Zero)))
      (ClTCons (Succ (Zero)) _ _ _ _ (Succ (Succ (Zero))) (ClApp (Succ (Zero)) _ _ (ClRef (Succ (Zero)) 3) (ClCons (Succ (Zero)) _ _ (ClBound (Succ (Zero)) (Zero) (LtZ (Zero))) (ClNil (Succ (Zero))))) (ClTNil (Succ (Succ (Zero)))))
      (ClTCons (Succ (Succ (Zero))) _ _ _ _ (Succ (Succ (Succ (Zero)))) (ClApp (Succ (Succ (Zero))) _ _ (ClBound (Succ (Succ (Zero))) (Zero) (LtZ (Succ (Zero)))) (ClCons (Succ (Succ (Zero))) _ _ (ClBound (Succ (Succ (Zero))) (Succ (Zero)) (LtS (Zero) (Succ (Zero)) (LtZ (Zero)))) (ClNil (Succ (Succ (Zero)))))) (ClTNil (Succ (Succ (Succ (Zero)))))))))

; Abstracting 7 out of the substituted term gives the original back, the two printed together.
(let (many u) (erased ap) (abstract (Cons _ (Some _ 7) (Nil _)) s))

; 7 occurs in the substituted term, so it cannot be assigned; 9 may be, its only binder being the return's own.
(let (many no7) (match many (assign-dec 0 7 s) (((Bool) r)) ((ADNo c d e q) (BTrue)) ((ADYes c d e q) (BFalse))))
(comptime-match no7 (BTrue))
(let (many yes9) (match many (assign-dec 0 9 s) (((Bool) r)) ((ADNo c d e q) (BFalse)) ((ADYes c d e q) (BTrue))))
(comptime-match yes9 (BTrue))
(Cons _ u $ Cons _ s $ Nil _)
