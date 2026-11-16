(def-adts
  ((NotIn : ((Ren) r) ((Nat) p) ((Nat) q) -> Type)
    enum
    (many NotInNil : (erased (Nat) p q) -> (NotIn (RNil) p q))
    (many NotInCons : (erased (Nat) p q a a') (erased (Ren) rest) (erased (Neq a p) n) (erased (Neq a' q) n') (erased (NotIn rest p q) ni)
       -> (NotIn (RCons a a' rest) p q))))

(def-fns _ $ (erased rena-notin : (erased (Ren) r) (erased (Nat) p q a a') (erased (NotIn r p q) ni) (subterm erased (RenA r a a') ra) ->
    (erased (Neq a p) n) (erased (Neq a' q) n'))
  (match erased ra _
    ((RenHere _ _ _) (let-match erased ni (NotInCons _ _ _ _ _ n n' _)) (values n n'))
    ((RenThere _ _ c c' rest _ _ ra1) (let-match erased ni (NotInCons _ _ _ _ _ _ _ ni1)) (rena-notin rest p q a a' ni1 ra1))))

(def-fns _ $ (erased rena-grow : (erased (Ren) r) (erased (Nat) p q a a') (erased (NotIn r p q) ni) (erased (RenA r a a') ra) ->
    (erased (RenA (RCons p q r) a a') out))
  (let ((erased n) (erased n')) (rena-notin r p q a a' ni ra))
  (RenThere a a' p q r n n' ra))

(def-fns _ $ (erased renw-grow : (erased (Ren) r) (erased (Nat) p q) (erased (Word) w w') (erased (NotIn r p q) ni) (erased (RenW r w w') rw) ->
    (erased (RenW (RCons p q r) w w') out))
  (match erased rw _
    ((RenImm _ n) (RenImm (RCons p q r) n))
    ((RenAddr _ a a' ra) (RenAddr (RCons p q r) a a' (rena-grow r p q a a' ni ra)))))

(def-fns _ $ (erased renws-grow : (erased (Ren) r) (erased (Nat) p q) (erased (List (Word)) ws ws') (erased (NotIn r p q) ni)
    (subterm erased (RenWs r ws ws') rws) -> (erased (RenWs (RCons p q r) ws ws') out))
  (match erased rws _
    ((RenWsNil _) (RenWsNil (RCons p q r)))
    ((RenWsCons _ w w' rest rest' rw rws1)
      (RenWsCons (RCons p q r) w w' rest rest' (renw-grow r p q w w' ni rw) (renws-grow r p q rest rest' ni rws1)))))

(def-fns _ $ (erased renb-grow : (erased (Ren) r) (erased (Nat) p q) (erased (Block) b b') (erased (NotIn r p q) ni) (erased (RenB r b b') rb) ->
    (erased (RenB (RCons p q r) b b') out))
  (let-match erased rb (MkRenB _ tag fs fs' rfs))
  (MkRenB (RCons p q r) tag fs fs' (renws-grow r p q fs fs' ni rfs)))

(def-fns _ $ (erased renh-grow : (erased (Ren) r) (erased (Nat) p q) (erased (Heap) h h') (erased (NotIn r p q) ni)
    (subterm erased (RenH r h h') rh) -> (erased (RenH (RCons p q r) h h') out))
  (match erased rh _
    ((RenHNil _) (RenHNil (RCons p q r)))
    ((RenHCons _ a a' b b' rest rest' ra rb rh1)
      (RenHCons (RCons p q r) a a' b b' rest rest' (rena-grow r p q a a' ni ra) (renb-grow r p q b b' ni rb) (renh-grow r p q rest rest' ni rh1)))))

(def-fns _ $ (erased renk-grow : (erased (Ren) r) (erased (Nat) p q) (erased (Stack) k k') (erased (NotIn r p q) ni)
    (subterm erased (RenK r k k') rk) -> (erased (RenK (RCons p q r) k k') out))
  (match erased rk _
    ((RenKNil _) (RenKNil (RCons p q r)))
    ((RenKLet _ env env' body k1 k1' re rk1)
      (RenKLet (RCons p q r) env env' body k1 k1' (renws-grow r p q env env' ni re) (renk-grow r p q k1 k1' ni rk1)))))

(def-fns _ $ (erased renc-grow : (erased (Ren) r) (erased (Nat) p q) (erased (Control) c c') (erased (NotIn r p q) ni) (erased (RenC r c c') rc) ->
    (erased (RenC (RCons p q r) c c') out))
  (match erased rc _
    ((RenCRun _ env env' code k k' re rk)
      (RenCRun (RCons p q r) env env' code k k' (renws-grow r p q env env' ni re) (renk-grow r p q k k' ni rk)))
    ((RenCRet _ w w' k k' rw rk)
      (RenCRet (RCons p q r) w w' k k' (renw-grow r p q w w' ni rw) (renk-grow r p q k k' ni rk)))))

(def-fns _ $ (erased ren-step-any : (erased (Ren) r) (erased (List (Code)) fns) (erased (Heap) h h') (erased (Control) c c') (erased (Nat) p q)
    (erased (Heap) h2) (erased (Control) c2)
    (erased (RenH r h h') rh) (erased (RenC r c c') rc) (erased (NotIn r p q) ni) (erased (Step fns h c (LAddr p) h2 c2) d) ->
    (erased (Heap) h2') (erased (Control) c2') (erased (Step fns h' c' (LAddr q) h2' c2') d')
    (erased (RenH (RCons p q r) h2 h2') rh2) (erased (RenC (RCons p q r) c2 c2') rc2))
  (ren-step (RCons p q r) fns h h' c c' (LAddr p) (LAddr q) h2 c2
    (renh-grow r p q h h' ni rh) (renc-grow r p q c c' ni rc) (RenLAddr (RCons p q r) p q (RenHere p q r)) d))
