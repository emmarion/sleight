; error: the scrutinee contradicts the facts in force
; No constructor survives; a let-match cannot export contradictory facts.
(def-adts $ (Indexed : ((Nat) i) -> Type) enum
  (many IZ : -> (Indexed (Zero)))
  (many IS : -> (Indexed (Succ (Zero)))))
(def-fns _ $ (many bad : (erased (Indexed (Succ (Succ (Zero)))) p) -> (many (Nat) n))
  (let-match erased p (IZ))
  0)
