; error: `M` is not a level minted by `def-lvl`
; The branch forces `M` equal to `L0`, but `prove-predates` reads its level by its binder, and the parameter
; `M` was minted by no `def-lvl`.
(def-lvl K)
(def-lvl L0)
(def-adts $ (AtLevel : ((Level) l) -> Type)
  enum
  (many Here : -> (AtLevel L0)))
(def-fns _ $ (many f : (erased (Level) M) (erased (AtLevel M) v) -> (many (Nat) r))
  (let ((erased p)) (match erased v (((Predates (Level) K M) q)) ((Here) (prove-predates K M))))
  0)
