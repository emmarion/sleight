(def-adts $ (Sem : -> Type)
  enum
  (many MkSem : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) Step) -> (Sem)))
(def-adts $ (Ex : ((Sem) s) -> Type)
  enum
  (many MkEx : (erased (TyCtor ((Nat) a) ((Nat) b) -> Type) Step) (erased (Step (Zero) (Zero)) p) -> (Ex (MkSem Step))))
(def-fns _ $ (erased use : (erased (Sem) sem) (erased (Ex sem) e) -> (erased (Nat) r))
  (let-match erased sem (MkSem step))
  (let-match erased e (MkEx st p))
  (let ((erased (step (Zero) (Zero)) w)) p)
  (Zero))
