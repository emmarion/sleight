(def-adts
  ((Found : (Type A) ((TyCtor (A x) -> Type) P) -> Type)
    enum
    (many FoundHit : (erased Type A) (erased (TyCtor (A x) -> Type) P) (many A x) (erased (P x) p) -> (Found A P))
    (many FoundMiss : (erased Type A) (erased (TyCtor (A x) -> Type) P) -> (Found A P))))

(def-fns _ $ (many atom-val-generic : (many (List (Word)) env) (many (Atom) a) -> (many (Found (Word) (AtomVal env a)) r))
  (FoundMiss _ _))
