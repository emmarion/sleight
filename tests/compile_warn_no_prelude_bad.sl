; prelude: none
; error: `compile-warn` needs the prelude's `String`, which `--no-prelude` leaves out
(def-adts $ (U : -> Type) enum (many MkU : -> (U)))
(let ((many u)) (MkU))
(compile-warn u)
