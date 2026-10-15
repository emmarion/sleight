; prelude: none
; error: `cell-same` needs the prelude's `ErasedOr`, which `--no-prelude` leaves out
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Box) b) -> (Box)))
(def-lvl L)
(def-fns L $ (many f : (many (Box) x) -> (many (Box) r))
  (let-match many x (MkBox b u))
  (let ((many s)) (cell-same u u))
  x)
