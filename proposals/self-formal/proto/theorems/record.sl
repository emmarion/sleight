(def-adts $ (Sem : -> Type)
  enum
  (many MkSem : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) Step) (erased (TyCtor ((Nat) a) -> Type) Final) -> (Sem)))
(def-fns _ $ (erased use : (erased (Sem) sem) (erased (Nat) a) (erased (Nat) b) -> (erased Type T))
  (let-match erased sem (MkSem step final))
  (step a b))
