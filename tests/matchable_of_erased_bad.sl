; error: `(matchable-of T)`, opened `erased` by an `open-adt`, used in a non-erased position
; error: <**>: note: the `open-adt` is here

(def-lvl X)
(def-fns X $ (many f : (erased (TyCtor -> Type) T) (erased (ValCtor -> (T)) C)
    (erased (Matchable enum T (many C)) m) -> (many (Matchable enum T (many C)) n))
  (open-adt erased m)
  (matchable-of T))
