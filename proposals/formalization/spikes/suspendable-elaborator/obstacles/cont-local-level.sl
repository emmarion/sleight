(def-fns W $ (many walk : (subterm many (Tree) t) -> (many (CM) m))
  (let-match many t (TNode l r) (else (CRet 1)))
  (def-fns _ $ (many after-l : (many (Nat) a) -> (many (CM) next))
    (walk r))
  (CBind (notail $ walk l) after-l))

(MkUnit)
