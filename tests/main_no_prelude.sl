; prelude: none
; stdin: hi
; error: a final function must be `(Fn L (many (String) x) -> (many (String) y))` or `(Fn L -> (many T y))`
(def-adts $ (String : -> Type) enum (many A : -> (String)) (many B : -> (String)))
(def-lvl M)
(def-fns M ((many main : (many (String) in) -> (many (String) out)) (B)))
main
