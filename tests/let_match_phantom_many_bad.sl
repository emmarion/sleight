; error: `Ghost` is phantom
(def-adts $ (OnlyGhost : -> Type) enum (erased Ghost : -> (OnlyGhost)))
(def-fns _ $ (many bad : (many (OnlyGhost) p) -> (many (Nat) n))
  (let-match many p (Ghost))
  0)
