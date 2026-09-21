; expect: (Cons _ 4 $ Cons _ 6 $ Nil _)
; Phantom evidence may be destructured at erased, including its declared-many fields.
(def-adts $ GhostIndex : ((Nat) i) -> Type enum
  (many RealIndex : -> (GhostIndex (Zero)))
  (erased GhostIndexOne : (many (Nat) x) -> (GhostIndex (Succ (Zero)))))
(def-adts $ OnlyGhost : -> Type enum
  (erased SoleGhost : (many (Nat) x) -> (OnlyGhost)))
(def-fns _ $ many ghost-value : (erased (GhostIndex (Succ (Zero))) p) -> (many (Nat) n)
  (let-match erased p (GhostIndexOne x))
  (let (erased (Eq (Nat) x x) equal) (Refl (Nat) x))
  4)
(def-fns _ $ many sole-value : (erased (OnlyGhost) p) -> (many (Nat) n)
  (let-match erased p (SoleGhost x))
  6)
(def-fns _ $ many ghost-main : -> (many (Nat) n)
  (ghost-value (GhostIndexOne 2)))
(def-fns _ $ many sole-main : -> (many (Nat) n)
  (sole-value (SoleGhost 3)))

(def-fns _ $ many phantom-tests : -> (many (List (Nat)) results)
  (Cons _ (ghost-main) (Cons _ (sole-main) (Nil _))))
phantom-tests
; warns: warning (line 5): phantom constructor GhostIndexOne has a many field
; warns: warning (line 7): phantom constructor SoleGhost has a many field
