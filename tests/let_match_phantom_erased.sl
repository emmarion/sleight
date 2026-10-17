; expect: (Cons _ 4 $ Cons _ 6 $ Nil _)
; Phantom evidence may be destructured at erased, including its declared-many fields.
(def-adts $ (GhostIndex : ((Nat) i) -> Type) enum
  (many RealIndex : -> (GhostIndex (Zero)))
  (erased GhostIndexOne : (many (Nat) x) -> (GhostIndex (Succ (Zero)))))
(def-adts $ (OnlyGhost : -> Type) enum
  (erased SoleGhost : (many (Nat) x) -> (OnlyGhost)))
(def-fns _ $ (many ghost-value : (erased (GhostIndex (Succ (Zero))) p) -> (many (Nat) n))
  (let-match erased p (GhostIndexOne x))
  (let ((erased (Eq (Nat) x x) _)) (Refl (Nat) x))
  4)
(def-fns _ $ (many sole-value : (erased (OnlyGhost) p) -> (many (Nat) n))
  (let-match erased p (SoleGhost _))
  6)
(def-fns _ $ (many ghost-main : -> (many (Nat) n))
  (ghost-value (GhostIndexOne 2)))
(def-fns _ $ (many sole-main : -> (many (Nat) n))
  (sole-value (SoleGhost 3)))

(def-fns _ $ (many phantom-tests : -> (many (List (Nat)) results))
  (Cons _ (ghost-main) (Cons _ (sole-main) (Nil _))))
phantom-tests
; warns: tests/let_match_phantom_erased.sl:5:3: warning: phantom constructor `GhostIndexOne` has a non-erased field
; warns: tests/let_match_phantom_erased.sl:7:3: warning: phantom constructor `SoleGhost` has a non-erased field
