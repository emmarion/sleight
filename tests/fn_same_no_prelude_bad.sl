; prelude: none
; error: `fn-same` needs the prelude's `ErasedOr`, which `--no-prelude` leaves out
(def-adts $ (Box : -> Type) enum (many MkBox : -> (Box)))
(def-lvl L)
(def-fns L $ (many f : (many (Box) x) -> (many (Box) r)) x)
(let ((many s)) (fn-same f f))
; fn-same: yes
