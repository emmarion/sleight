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

(def-adts $ (Certified : -> Type)
  enum
  (many MkCertified : (erased (Level) L) (many (Fn L (many (Src) s) -> (many (Verdict s) r)) c)
     (erased (Fn L (erased (Src) s) (erased (Elab s) d) (erased (Fails s) f) -> (erased (False) no)) excl) -> (Certified)))
(goal many (Certified))
