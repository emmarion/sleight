(def-fns _ $ (many no-lpo : (erased (Level) K)
    (erased (Fn K (erased (Level) N) (erased (Level) D) (erased (Level) E)
        (erased (TyCtor ((Nat) n) -> Type) Q)
        (erased (Fn D (erased (Nat) n) -> (erased (Or (Q n) (Fn E (erased (Q n) q) -> (erased (False) f))) r)) dec) ->
        (erased (Or (Ex Q) (Fn N (erased (Nat) n) (erased (Q n) q) -> (erased (False) f))) r)) lpo) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl N)
  (def-adts $ (Bad : ((Nat) i) -> Type)
    enum
    (many MkBad : (erased (Nat) i) (many (Fn N (erased (Nat) n) (erased (Bad n) q) -> (erased (False) f)) g) -> (Bad i)))
  (def-fns K $ (erased dec : (erased (Nat) n) -> (erased (Or (Bad n) (Fn N (erased (Bad n) q) -> (erased (False) f))) r))
    (def-fns N $ (erased omega : (erased (Bad n) q) -> (erased (False) f))
      (let-match erased q (MkBad _ g))
      (g n q))
    (Inr _ _ omega))
  (def-fns _ $ (many absurd absurd absurdity : -> (many (False) f))
    (match erased (lpo N K N Bad dec) _
      (absurd (Inl _ _ x) (let-match erased x (MkEx _ n q)) (let-match erased q (MkBad _ g)) (g n q))
      (absurd (Inr _ _ h) (h (Zero) (MkBad (Zero) h)))))
  (values (level-of absurdity) absurdity))
