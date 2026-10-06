; error: this `let-match` is missing a branch for the following unrefuted constructor:
; error: note: value constructor `IS`, which is declared here
; Refining the selected constructor first would unsoundly refute the alternative.
(def-adts $ (Indexed : ((Nat) i) -> Type) enum
  (many IZ : -> (Indexed (Zero)))
  (many IS : -> (Indexed (Succ (Zero)))))
(def-fns _ $ (many bad : (erased (Nat) i) (erased (Indexed i) p) -> (erased (Eq (Nat) i (Zero)) q))
  (let-match erased p (IZ))
  (Refl (Nat) i))
