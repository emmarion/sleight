; error: this `let-match` is missing a branch for the following unrefuted constructor:
; error: note: value constructor `GhostB`, which is declared here
; Erased phantom matching still requires every other constructor to be refuted.
(def-adts $ (Both : -> Type) enum
  (erased GhostA : -> (Both))
  (erased GhostB : -> (Both)))
(def-fns _ $ (many bad : (erased (Both) p) -> (many (Nat) n))
  (let-match erased p (GhostA))
  0)
