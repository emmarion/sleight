; error: is not a constructor of
(def-fns _ $ erased bad :
  (erased (TyCtor -> Type) T)
  (erased (ValCtor -> (T)) C)
  (erased (Matchable enum T) m) -> (erased Type r)
  (open-adt erased m)
  (Cell C))
