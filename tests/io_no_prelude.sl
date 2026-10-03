; prelude: none
; expect: (B)
(def-adts $ (IO : -> Type) enum (many A : -> (IO)) (many B : -> (IO)))
(B)
