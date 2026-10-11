; prelude: none
; error: `P` has no `Matchable` open
(def-opaque $ (P : -> Type))
(def-prim $ (erased gensym-unique : -> (erased (P) p)))
(def-fns _ $ (erased f : (erased (P) p) -> (erased Type t))
  (match erased p _))
