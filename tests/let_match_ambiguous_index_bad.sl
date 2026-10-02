; error: needs a branch for it
; Refining the selected constructor first would unsoundly refute the alternative.
(def-adts $ (Indexed : ((Nat) i) -> Type) enum
  (many IZ : -> (Indexed (Zero)))
  (many IS : -> (Indexed (Succ (Zero)))))
(def-fns _ $ (many bad : (erased (Nat) i) (erased (Indexed i) p) -> (erased (Eq (Nat) i (Zero)) q))
  (let-match erased p (IZ))
  (Refl (Nat) i))
