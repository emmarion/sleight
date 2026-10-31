; prelude: none
; error: `imm` needs the prelude's `Imm`, which `--no-prelude` leaves out
(def-adts $ (Box : -> Type) enum (many MkBox : (many (Box) b) -> (Box)))
(def-fns _ $ (many f : (unique (Box) b) (many (Box) c) -> (unique (Box) r at b))
  (let-match unique b (MkBox d u))
  (u (imm d c) c))
