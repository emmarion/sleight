(def-adts
  ((RenK : ((Ren) r) ((Stack) k) ((Stack) k') -> Type)
    enum
    (many RenKNil : (erased (Ren) r) -> (RenK r (KNil) (KNil)))
    (many RenKLet : (erased (Ren) r) (erased (List (Word)) env env') (erased (Code) body) (erased (Stack) k k')
       (erased (RenWs r env env') re) (erased (RenK r k k') rk) -> (RenK r (KLet env body k) (KLet env' body k'))))
  ((RenC : ((Ren) r) ((Control) c) ((Control) c') -> Type)
    enum
    (many RenCRun : (erased (Ren) r) (erased (List (Word)) env env') (erased (Code) c) (erased (Stack) k k')
       (erased (RenWs r env env') re) (erased (RenK r k k') rk) -> (RenC r (KRun env c k) (KRun env' c k')))
    (many RenCRet : (erased (Ren) r) (erased (Word) w w') (erased (Stack) k k')
       (erased (RenW r w w') rw) (erased (RenK r k k') rk) -> (RenC r (KRet w k) (KRet w' k'))))
  ((RenLs : ((Ren) r) ((List (Label)) ls) ((List (Label)) ls') -> Type)
    enum
    (many RenLsNil : (erased (Ren) r) -> (RenLs r (Nil (Label)) (Nil (Label))))
    (many RenLsCons : (erased (Ren) r) (erased (Label) l l') (erased (List (Label)) ls ls') (erased (RenL r l l') p) (erased (RenLs r ls ls') q)
       -> (RenLs r (Cons (Label) l ls) (Cons (Label) l' ls')))))

(def-fns _ $ (erased ren-step : (erased (Ren) r) (erased (List (Code)) fns) (erased (Heap) h h') (erased (Control) c c') (erased (Label) l l')
    (erased (Heap) h2) (erased (Control) c2)
    (erased (RenH r h h') rh) (erased (RenC r c c') rc) (erased (RenL r l l') rl) (erased (Step fns h c l h2 c2) d) ->
    (erased (Heap) h2') (erased (Control) c2') (erased (Step fns h' c' l' h2' c2') d') (erased (RenH r h2 h2') rh2) (erased (RenC r c2 c2') rc2))
  (match erased d _
    ((StDo _ _ env i k _ _ w p)
      (let-match erased rc (RenCRun _ _ env' _ _ k' re rk))
      (let ((erased h2') (erased w') (erased p') (erased rh2) (erased rw)) (ren-prim r h h' env env' i l l' h2 w rh re rl p))
      (values h2' (KRet w' k') (StDo fns h' env' i k' l' h2' w' p') rh2 (RenCRet r w w' k k' rw rk)))
    ((StLet _ _ env rhs body k)
      (let-match erased rc (RenCRun _ _ env' _ _ k' re rk))
      (let-match erased rl (RenLTau _))
      (values h' (KRun env' rhs (KLet env' body k')) (StLet fns h' env' rhs body k') rh
        (RenCRun r env env' rhs (KLet env body k) (KLet env' body k') re (RenKLet r env env' body k k' re rk))))
    ((StRet _ _ w env body k)
      (let-match erased rc (RenCRet _ _ w' _ kk' rw rkk))
      (let-match erased rkk (RenKLet _ _ env' _ _ k' re rk))
      (let-match erased rl (RenLTau _))
      (values h' (KRun (Cons _ w' env') body k') (StRet fns h' w' env' body k') rh
        (RenCRun r (Cons _ w env) (Cons _ w' env') body k k' (RenWsCons r w w' env env' rw re) rk)))
    ((StMatch _ _ env a blocks imms k v body fs env2 pa sel ct)
      (let-match erased rc (RenCRun _ _ env' _ _ k' re rk))
      (let-match erased rl (RenLTau _))
      (let ((erased v') (erased pa') (erased rv)) (ren-atomval r env env' a v re pa))
      (let ((erased fs') (erased sel') (erased rfs)) (ren-select r h h' v v' blocks imms body fs rh rv sel))
      (let ((erased env2') (erased ct') (erased re2)) (ren-cat r fs env env2 fs' env' ct rfs re))
      (values h' (KRun env2' body k') (StMatch fns h' env' a blocks imms k' v' body fs' env2' pa' sel' ct') rh
        (RenCRun r env2 env2' body k k' re2 rk)))
    ((StCall _ _ env f args k body ws pf pa)
      (let-match erased rc (RenCRun _ _ env' _ _ k' re rk))
      (let-match erased rl (RenLTau _))
      (let ((erased ws') (erased pa') (erased rws)) (ren-atomvals r env env' args ws re pa))
      (values h' (KRun ws' body k') (StCall fns h' env' f args k' body ws' pf pa') rh (RenCRun r ws ws' body k k' rws rk)))))

(def-fns _ $ (erased ren-steps : (erased (Ren) r) (erased (List (Code)) fns) (erased (Heap) h h') (erased (Control) c c') (erased (List (Label)) ls ls')
    (erased (Heap) h2) (erased (Control) c2)
    (erased (RenH r h h') rh) (erased (RenC r c c') rc) (erased (RenLs r ls ls') rl) (subterm erased (Steps fns h c ls h2 c2) d) ->
    (erased (Heap) h2') (erased (Control) c2') (erased (Steps fns h' c' ls' h2' c2') d') (erased (RenH r h2 h2') rh2) (erased (RenC r c2 c2') rc2))
  (match erased d _
    ((StepsNil _ _ _)
      (let-match erased rl (RenLsNil _))
      (values h' c' (StepsNil fns h' c') rh rc))
    ((StepsCons _ _ _ l h1 c1 rest _ _ p q)
      (let-match erased rl (RenLsCons _ _ l' _ rest' rl1 rl2))
      (let ((erased h1') (erased c1') (erased p') (erased rh1) (erased rc1)) (ren-step r fns h h' c c' l l' h1 c1 rh rc rl1 p))
      (let ((erased h2') (erased c2') (erased q') (erased rh2) (erased rc2)) (ren-steps r fns h1 h1' c1 c1' rest rest' h2 c2 rh1 rc1 rl2 q))
      (values h2' c2' (StepsCons fns h' c' l' h1' c1' rest' h2' c2' p' q') rh2 rc2))))
