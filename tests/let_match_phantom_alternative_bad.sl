; error: this `let-match` is missing a branch for the following unrefuted constructor:
; error: note: value constructor `Ghost`, which is declared here
; A phantom alternative is not automatically refuted, even under many.
(def-adts $ (Both : -> Type) enum
  (many Real : -> (Both))
  (erased Ghost : -> (Both)))
(def-fns _ $ (many bad : (many (Both) p) -> (many (Nat) n))
  (let-match many p (Real))
  0)
