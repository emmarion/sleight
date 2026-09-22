; error: erased value x
; warns: warning (line 5): phantom constructor Ghost has a non-erased field
; Declared-many fields of a phantom matched at erased stay erased.
(def-adts $ OnlyGhost : -> Type enum
  (erased Ghost : (many (Nat) x) -> (OnlyGhost)))
(def-fns _ $ many bad : (erased (OnlyGhost) p) -> (many (Nat) n)
  (let-match erased p (Ghost x))
  x)
