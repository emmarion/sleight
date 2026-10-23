; needs: ../std/macro
(def-macro (placed args here)
  (let-match many args (Nil _) ((Cons _ _ _) (qq (BFalse))))
  (match many here _ ((MkPos _ _ _) (qq (BTrue))) ((NoPos) (qq (BFalse)))))

(def-macro (doubled args here mw)
  (let-match many args (Cons _ n rest) ((Nil _) (macro-fail mw here "`doubled` takes one number")))
  (let-match many rest (Nil _) ((Cons _ _ _) (macro-fail mw here "`doubled` takes one number")))
  (let ((unique mw1) (many v)) (arg-nat mw n))
  (let-match many v (Some _ k) ((None _) (macro-fail mw1 here "`doubled` takes a constant")))
  (let ((unique mw2) (many r)) (nat-raw mw1 here $ nat-add k k))
  (values mw2 $ Cons _ r $ Nil _))

(MkPair _ _ (placed) (doubled 21))
; expect: (MkPair _ _ (BTrue) 42)
