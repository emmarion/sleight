; error: phantom constructors have no cells
(def-fns _ $ erased bad :
  (erased (TyCtor -> Type) T)
  (erased (ValCtor -> (T)) C)
  (erased (Matchable enum T (erased C)) m) -> (erased Type r)
  (open-adt erased m)
  (Cell C))
