(def-adts $ (EngE : -> Type)
  enum
  (many MkEngE : (many (Nat) h) (many (Maybe (Eng h)) e) -> (EngE)))

(def-fns _ $ (many r4-eng-lookup : (many (Nat) h) (subterm many (List (EngE)) cache) -> (many (Maybe (Maybe (Eng h))) r))
  (let-match many cache (Cons _ x rest) ((Nil _) (None _)))
  (let-match many x (MkEngE h2 e))
  (match many (nat-eq h2 h) _ ((Equal _ _ _) (Some _ e)) ((Unequal _ _ _ _ _) (tail $ r4-eng-lookup h rest))))

; red4's fcache.
(def-adts $ (R4St : -> Type)
  enum
  (many MkR4St : (many (List (EngE)) cache) -> (R4St)))

; The Kempe tree kt of cp, whose ring has h + 2 darts, is sound for the ring traces of cp's map.
(def-adts $ (KChk : ((List (Step)) cp) -> Type)
  enum
  (many KCYes : (erased (List (Step)) cp) (many (Nat) h) (erased (Ctree) kt) (many (R4Out h kt) ro) (erased (KSound (MkPred (List (Step)) cp CpColR) h kt) ks)
      (erased (Cprsize cp (Succ (Succ h))) cs) (erased (NoA cp) na) -> (KChk cp))
  (many KCNo : (erased (List (Step)) cp) -> (KChk cp)))

