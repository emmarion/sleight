(def-fns _ $ (many settle-bad : (erased (List $ Stmt) p0) (many (List $ Ent) es) (erased (Tm) t) (many (List $ Stmt) rest)
    (erased (Ctx p0 es (Cons (Stmt) (Let t) rest)) c) (erased (List $ Val) env) (erased (Vals es env) ve) -> (many (Turn CState p0) o))
  (More CState p0 $ Checking p0 (Cons (Ent) (MkEnt (VNum 0) (KNone)) es) rest
    (CLet p0 es t rest (VNum 0) c (MkEvals es t (VNum 0) env ve (RunHalt _ _ (SRetNil (VNum 0)))))))
