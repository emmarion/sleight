(def-adts
  ((Tight : ((Ren) r) ((Heap) h) ((Heap) h') -> Type)
    enum
    (many TightNil : (erased (Heap) h h') -> (Tight (RNil) h h'))
    (many TightCons : (erased (Nat) a a') (erased (Ren) rest) (erased (Heap) h h') (erased (Block) b b')
       (erased (Lookup h a b) lk) (erased (Lookup h' a' b') lk') (erased (Tight rest h h') t) -> (Tight (RCons a a' rest) h h'))))

(def-fns _ $ (erased tight-not-in : (erased (Ren) r) (erased (Heap) h h') (erased (Nat) p q)
    (subterm erased (Tight r h h') t) (erased (Fresh h p) f) (erased (Fresh h' q) f') -> (erased (NotIn r p q) ni))
  (match erased t _
    ((TightNil _ _) (NotInNil p q))
    ((TightCons a a' rest _ _ b b' lk lk' t1)
      (NotInCons p q a a' rest (lookup-fresh-neq h a p b lk f) (lookup-fresh-neq h' a' q b' lk' f') (tight-not-in rest h h' p q t1 f f')))))

(def-fns _ $ (erased step-keeps : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) (erased (Label) l) (erased (Heap) h2) (erased (Control) c2)
    (erased (Nat) x) (erased (Block) b) (erased (Step fns h c l h2 c2) d) (erased (Lookup h x b) lx) ->
    (erased (Block) b2) (erased (Lookup h2 x b2) lk) (erased (Shape b b2) s))
  (match erased d _
    ((StDo _ _ env i _ _ _ w p) (prim-keeps h env i l h2 w x b p lx))
    ((StLet _ _ _ _ _ _) (values b lx (shape-refl b)))
    ((StRet _ _ _ _ _ _) (values b lx (shape-refl b)))
    ((StMatch _ _ _ _ _ _ _ _ _ _ _ _ _ _) (values b lx (shape-refl b)))
    ((StCall _ _ _ _ _ _ _ _ _ _) (values b lx (shape-refl b)))))

(def-fns _ $ (erased tight-step : (erased (Ren) r) (erased (List (Code)) fns) (erased (Heap) h h') (erased (Control) c c') (erased (Label) l l')
    (erased (Heap) h2 h2') (erased (Control) c2 c2')
    (subterm erased (Tight r h h') t) (erased (Step fns h c l h2 c2) d) (erased (Step fns h' c' l' h2' c2') d') -> (erased (Tight r h2 h2') t2))
  (let-match erased t (TightCons a a' rest _ _ b b' lk lk' t1) ((TightNil _ _) (TightNil h2 h2')))
  (let ((erased b2) (erased lk2) (erased _)) (step-keeps fns h c l h2 c2 a b d lk))
  (let ((erased b2') (erased lk2') (erased _)) (step-keeps fns h' c' l' h2' c2' a' b' d' lk'))
  (TightCons a a' rest h2 h2' b2 b2' lk2 lk2' (tight-step rest fns h h' c c' l l' h2 h2' c2 c2' t1 d d')))

(def-fns _ $ (erased step-alloc-live : (erased (List (Code)) fns) (erased (Heap) h) (erased (Control) c) (erased (Nat) p) (erased (Heap) h2) (erased (Control) c2)
    (erased (Step fns h c (LAddr p) h2 c2) d) -> (erased (Block) blk) (erased (Lookup h2 p blk) lk))
  (let-match erased d (StDo _ _ _ _ _ _ _ _ pr))
  (match erased pr _
    ((PCon _ _ tag _ ws _ _ _ al) (let-match erased al (MkAlloc _ _ _ _)) (values (MkBlock tag ws) (LkHere p (MkBlock tag ws) h)))
    ((PCopy _ _ _ _ _ _ blk _ _ _ al) (let-match erased al (MkAlloc _ _ _ _)) (values blk (LkHere p blk h)))))

(def-fns _ $ (erased sim-alloc : (erased (Ren) r) (erased (List (Code)) fns) (erased (Heap) h h') (erased (Control) c c') (erased (Nat) p q)
    (erased (Heap) h2) (erased (Control) c2)
    (erased (RenH r h h') rh) (erased (RenC r c c') rc) (erased (Tight r h h') t)
    (erased (Step fns h c (LAddr p) h2 c2) d) (erased (Fresh h' q) f') ->
    (erased (Heap) h2') (erased (Control) c2') (erased (Step fns h' c' (LAddr q) h2' c2') d')
    (erased (RenH (RCons p q r) h2 h2') rh2) (erased (RenC (RCons p q r) c2 c2') rc2) (erased (Tight (RCons p q r) h2 h2') t2))
  (let ((erased ni)) (tight-not-in r h h' p q t (step-label-fresh fns h c p h2 c2 d) f'))
  (let ((erased h2') (erased c2') (erased d') (erased rh2) (erased rc2)) (ren-step-any r fns h h' c c' p q h2 c2 rh rc ni d))
  (let ((erased blk) (erased lk)) (step-alloc-live fns h c p h2 c2 d))
  (let ((erased blk') (erased lk')) (step-alloc-live fns h' c' q h2' c2' d'))
  (values h2' c2' d' rh2 rc2
    (TightCons p q r h2 h2' blk blk' lk lk' (tight-step r fns h h' c c' (LAddr p) (LAddr q) h2 h2' c2 c2' t d d'))))

(def-adts
  ((Quiet : ((Label) l) -> Type)
    enum
    (many QTau : -> (Quiet (LTau)))
    (many QYes : -> (Quiet (LYes)))
    (many QNo : -> (Quiet (LNo)))))

(def-fns _ $ (erased sim-quiet : (erased (Ren) r) (erased (List (Code)) fns) (erased (Heap) h h') (erased (Control) c c') (erased (Label) l)
    (erased (Heap) h2) (erased (Control) c2)
    (erased (RenH r h h') rh) (erased (RenC r c c') rc) (erased (Tight r h h') t) (erased (Quiet l) ql) (erased (Step fns h c l h2 c2) d) ->
    (erased (Heap) h2') (erased (Control) c2') (erased (Step fns h' c' l h2' c2') d')
    (erased (RenH r h2 h2') rh2) (erased (RenC r c2 c2') rc2) (erased (Tight r h2 h2') t2))
  (let ((erased (RenL r l l) rl)) (match erased ql _ ((QTau) (RenLTau r)) ((QYes) (RenLYes r)) ((QNo) (RenLNo r))))
  (let ((erased h2') (erased c2') (erased d') (erased rh2) (erased rc2)) (ren-step r fns h h' c c' l l h2 c2 rh rc rl d))
  (values h2' c2' d' rh2 rc2 (tight-step r fns h h' c c' l l h2 h2' c2 c2' t d d')))
