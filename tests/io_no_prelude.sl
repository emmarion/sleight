; prelude: none
; expect: (B)
(def-adts $ (Program : -> Type) enum (many A : -> (Program)) (many B : -> (Program)))
(B)
