(def-adts $ (Certified : -> Type)
  enum
  (many MkCertified : (erased (TyCtor ((List $ Stmt) p) -> Type) S) (erased (Level) L)
     (many (Fn L (many (List $ Stmt) p) -> (many (S p) s)) init)
     (many (Fn L (erased (List $ Stmt) p) (many (S p) s) -> (many (Turn S p) t)) step)
     (erased (Fn L (erased (List $ Stmt) p) (erased (Elab (Nil (Ent)) p) d) (erased (Fails (Nil (Ent)) p) f) ->
        (erased (False) no)) excl)
     -> (Certified)))
(goal many (Certified))
