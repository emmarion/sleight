(def-fns _
  ((many init-top : (many (List $ Stmt) p) -> (many (RState p) s)) (rstart p))
  ((many step-top : (erased (List $ Stmt) p) (many (RState p) s) -> (many (Turn RState p) t)) (rstep p s))
  ((erased excl-top : (erased (List $ Stmt) p) (erased (Elab (Nil (Ent)) p) d) (erased (Fails (Nil (Ent)) p) f) ->
      (erased (False) no))
    (exclusive (Nil (Ent)) p d f)))
(qed (MkCertified RState _ init-top step-top excl-top))
