(def-adts $ (Src : -> Type)
  enum
  (many Lit : (many (Nat) n) -> (Src))
  (many Plus : (many (Src) a) (many (Src) b) -> (Src))
  (many Bad : -> (Src)))

(def-adts $ (Elab : ((Src) s) -> Type)
  enum
  (many ElLit : (erased (Nat) n) -> (Elab (Lit n)))
  (many ElPlus : (erased (Src) a) (erased (Src) b) (erased (Elab a) da) (erased (Elab b) db) -> (Elab (Plus a b))))

(def-adts $ (Fails : ((Src) s) -> Type)
  enum
  (many FBad : -> (Fails (Bad)))
  (many FPlusL : (erased (Src) a) (erased (Src) b) (erased (Fails a) fa) -> (Fails (Plus a b)))
  (many FPlusR : (erased (Src) a) (erased (Src) b) (erased (Fails b) fb) -> (Fails (Plus a b))))

(def-adts $ (Verdict : ((Src) s) -> Type)
  enum
  (many Accepted : (erased (Src) s) (erased (Elab s) d) -> (Verdict s))
  (many Rejected : (erased (Src) s) (erased (Fails s) f) -> (Verdict s)))

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

(compile (Plus (Lit 1) (Lit 2)))
