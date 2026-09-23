; error: needs an ordinary `match`
; A unique surviving constructor is insufficient if the pattern names another.
(def-adts $ (Indexed : ((Nat) i) -> Type) enum
  (many IZ : -> (Indexed (Zero)))
  (many IS : -> (Indexed (Succ (Zero)))))
(def-fns _ $ (many bad : (erased (Indexed (Succ (Zero))) p) -> (many (Nat) n))
  (let-match erased p (IZ))
  0)
