; error: needs an ordinary match
; A phantom alternative is not automatically refuted, even under many.
(def-adts $ (Both : -> Type) enum
  (many Real : -> (Both))
  (erased Ghost : -> (Both)))
(def-fns _ $ (many bad : (many (Both) p) -> (many (Nat) n))
  (let-match many p (Real))
  0)
