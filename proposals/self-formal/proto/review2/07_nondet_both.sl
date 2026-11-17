; Second review of 07: with one extra, nondeterministic Step rule (SNumUp in 07_nondet_spec.sl), the program
; `Let (Num 0); Assert 0 CSucc` has both an Elab and a Fails derivation, so exclusivity fails. Run after
; 07_nondet_spec.sl.
(let ((many p)) (Cons _ (Let $ Num (Zero)) $ Cons _ (Assert (Zero) (CSucc)) $ Nil _))
(let ((erased one)) (VNum (Succ (Zero))))
(let ((erased zero)) (VNum (Zero)))
(let ((erased run1)) (RunGo _ (Rt one $ Nil _) _ (SNumUp (Zero) (Nil _) (Nil _)) (RunHalt _ _ (SRetNil one))))
(let ((erased run0)) (RunGo _ (Rt zero $ Nil _) _ (SNum (Zero) (Nil _) (Nil _)) (RunHalt _ _ (SRetNil zero))))
(let ((erased ok)) (ElLet (Nil _) (Num (Zero)) _ one (MkEvals _ _ _ (Nil _) (ValsNil) run1)
  (ElAssert _ (Zero) (CSucc) (Nil _) one (KNone) _ (NthHere _ _ _) (HSucc (Zero)) (SetHere _ _ _ _) (ElNil _))))
(let ((erased bad)) (FLetRest (Nil _) (Num (Zero)) _ zero (MkEvals _ _ _ (Nil _) (ValsNil) run0)
  (FAssertHead _ (Zero) (CSucc) (Nil _) zero (KNone) (CZero) (NthHere _ _ _) (HZero) (NeSZ))))
(def-adts $ (Both : ((List $ Stmt) q) -> Type)
  enum
  (many MkBoth : (erased (List $ Stmt) q) (erased (Elab (Nil (Ent)) q) d) (erased (Fails (Nil (Ent)) q) f) -> (Both q)))
(MkBoth p ok bad)
