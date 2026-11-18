; Accepted (round-6 review of 06): one result type, indexed by an unapplied relation, serves run-op.
; Needs std/list.sl, spec.sl and machine.sl first.
(def-adts $ (Out2 : (Type T1) (T1 a1) (Type T2) (T2 a2) (Type W) ((TyCtor (T1 b1) (T2 b2) (W w) -> Type) R) -> Type)
  enum
  (many Found2 : (erased Type T1) (erased T1 a1) (erased Type T2) (erased T2 a2) (erased Type W)
     (erased (TyCtor (T1 b1) (T2 b2) (W w) -> Type) R) (many W x) (erased (R a1 a2 x) p) -> (Out2 T1 a1 T2 a2 W R))
  (many Missing2 : (erased Type T1) (erased T1 a1) (erased Type T2) (erased T2 a2) (erased Type W)
     (erased (TyCtor (T1 b1) (T2 b2) (W w) -> Type) R) -> (Out2 T1 a1 T2 a2 W R)))
(def-fns _ $ (many run-op2 : (many (Mem) m) (many (Op) o) -> (many (Out2 (Mem) m (Op) o (Mem) RunOp) r))
  (let-match many (run-op m o) (OpOk _ _ m2 rr) ((OpNo _ _) (Missing2 _ _ _ _ _ _)))
  (Found2 _ _ _ _ _ _ m2 rr))
(run-op2 (MkMem (Cons _ (VNum 0) $ Nil _) $ Nil _) (OSet (Zero) 7))
