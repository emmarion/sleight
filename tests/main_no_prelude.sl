; prelude: none
; stdin: hi
; expect: _
(def-adts $ (String : -> Type) enum (many A : -> (String)) (many B : -> (String)))
(def-lvl M)
(def-fns M ((many main : (many (String) in) -> (many (String) out)) (B)))
main
