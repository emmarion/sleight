; prelude: none
; error: a second `def-prim` for `gensym-unique`
(def-prim $ (erased gensym-unique : -> ))
(def-prim $ (erased gensym-unique : -> ))
