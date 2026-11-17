(def-fns _ $ (many compile : (subterm many (Src) s) -> (many (Verdict s) r))
  (match many s _
    ((Lit n) (Accepted _ (ElLit n)))
    ((Bad) (Rejected _ (FBad)))
    ((Plus a b)
      (let ((many va)) (compile a))
      (match many va _
        ((Rejected _ fa) (Rejected _ (FPlusL a b fa)))
        ((Accepted _ da)
          (let ((many vb)) (compile b))
          (match many vb _
            ((Rejected _ fb) (Rejected _ (FPlusR a b fb)))
            ((Accepted _ db) (Accepted _ (ElPlus a b da db)))))))))

(def-fns _ $ (erased exclusive : (subterm erased (Src) s) (erased (Elab s) d) (erased (Fails s) f) -> (erased (False) no))
  (match erased f _
    ((FBad) (match erased d _))
    ((FPlusL a b fa)
      (let-match erased d (ElPlus _ _ da db))
      (exclusive a da fa))
    ((FPlusR a b fb)
      (let-match erased d (ElPlus _ _ da db))
      (exclusive b db fb))))


(def-fns _ $ (many compile-top : (many (Src) s) -> (many (Verdict s) r)) (compile s))
(def-fns _ $ (erased excl-top : (erased (Src) s) (erased (Elab s) d) (erased (Fails s) f) -> (erased (False) no)) (exclusive s d f))
(qed (MkCertified _ compile-top _ excl-top))
