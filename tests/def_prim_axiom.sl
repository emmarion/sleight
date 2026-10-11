; prelude: none
(def-opaque $ (P : (Type A) -> Type))
(def-prim $ (erased gensym-unique : (erased Type A) -> (erased (P A) p)))
(let ((erased q)) (gensym-unique Type))
