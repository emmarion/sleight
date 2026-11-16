(def-adts $ (SM : -> Type)
  enum
  (many SRet : (many (Nat) v) -> (SM))
  (many SBind : (many (SM) m) (many (Fn W (many (Nat) v) -> (many (SM) next)) f) -> (SM)))

(def-fns W $ (many walk : (subterm many (Tree) t) -> (many (SM) m))
  (let-match many t (TNode l r) (else (SRet 1)))
  (def-fns W $ (many after-l : (many (Nat) a) -> (many (SM) next))
    (walk r))
  (SBind (notail $ walk l) after-l))

(MkUnit)
