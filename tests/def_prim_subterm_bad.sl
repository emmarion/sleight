; prelude: none
; error: `subterm` is not allowed here
(def-opaque $ (P : (Type A) -> Type))
(def-prim $ (erased gensym-unique : (subterm erased Type A) -> (erased (P A) p)))
