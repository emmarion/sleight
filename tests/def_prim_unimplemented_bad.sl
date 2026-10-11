; prelude: none
; error: the compilers have no implementation of `gensym-unique`, so its returns must be erased
(def-opaque $ (P : -> Type))
(def-prim $ (many gensym-unique : -> (many (P) p)))
