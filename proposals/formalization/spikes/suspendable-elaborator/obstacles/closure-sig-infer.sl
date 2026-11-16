(def-fns W $ (many walk : (subterm many (Tree) t) -> (many (CM) m))
  (let-match many t (TNode l r) (else (CRet 1)))
  (def-fns K $ (many after-l : (many _ a) -> (many _ next))
    (walk r))
  (CBind (notail $ walk l) after-l))

(MkUnit)
