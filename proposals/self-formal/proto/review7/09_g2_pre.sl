(def-adts $ (False : -> Type) enum)
(def-adts $ (String : -> Type) enum (many SNil : -> (String)))
(def-prim $ (erased gensym-unique : (erased Type A) -> (erased A x)))
