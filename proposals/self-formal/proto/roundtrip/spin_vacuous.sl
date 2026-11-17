(def-adts $ (Spin : ((List $ Stmt) p) -> Type)
  enum
  (many MkSpin : (erased (List $ Stmt) p) -> (Spin p)))
(def-fns _
  ((many init-top : (many (List $ Stmt) p) -> (many (Spin p) s)) (MkSpin p))
  ((many step-top : (erased (List $ Stmt) p) (many (Spin p) s) -> (many (Turn Spin p) t)) (More Spin p s))
  ((erased excl-top : (erased (List $ Stmt) p) (erased (Elab (Nil (Ent)) p) d) (erased (Fails (Nil (Ent)) p) f) ->
      (erased (False) no))
    (exclusive (Nil (Ent)) p d f)))
(qed (MkCertified Spin _ init-top step-top excl-top))
