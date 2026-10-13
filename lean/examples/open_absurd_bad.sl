
(def-lvl X)
(def-fns X $ (many f : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C) (erased (ValCtor -> (T)) D)
    (erased (Matchable enum T (many C) (many D)) m) -> (many (Nat) n))
  (open-absurd m _))
f
