(def-fns _ $ (erased prim-det-nolabel : (erased (Heap) h) (erased (List (Word)) env) (erased (Atom) a b) (erased (Label) l1 l2)
    (erased (Heap) h1 h2) (erased (Word) w1 w2)
    (erased (Prim h env (ISame a b) l1 h1 w1) d1) (erased (Prim h env (ISame a b) l2 h2 w2) d2) ->
    (erased (Eq (Word) w1 w2) ew))
  (match erased d1 _
    ((PSameYes _ _ _ _ _ _ _)
      (let-match erased d2 (PSameYes _ _ _ _ _ _ _))
      (Refl _ w1))
    ((PSameNo _ _ _ _ _ _ _ _)
      (let-match erased d2 (PSameNo _ _ _ _ _ _ _ _))
      (Refl _ w1))))
