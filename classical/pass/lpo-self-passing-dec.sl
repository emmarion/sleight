(def-fns _ $ (many no-lpo : (erased (Level) K)
    (erased (Fn K (erased (Level) N) (erased (Level) D) (erased (Level) E)
        (erased (Predates (Level) E N) en)
        (erased (TyCtor ((Nat) n) -> Type) Q)
        (erased (Fn D (erased (Nat) n) -> (erased (Or (Q n) (Fn E (erased (Q n) q) -> (erased (False) f))) r)) dec) ->
        (erased (Or (Ex Q) (Fn N (erased (Nat) n) (erased (Q n) q) -> (erased (False) f))) r)) lpo) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl E)
  (def-lvl N)
  (let ((erased en)) (prove-predates E N))
  (def-adts $ (Bad : ((Nat) i) -> Type)
    enum
    (many MkBad : (erased (Nat) i) (many (Fn N (erased (Nat) n) (erased (Bad n) q) -> (erased (False) f)) g) -> (Bad i)))
  (def-fns _ $ (erased dec : (erased (Nat) n) -> (erased (Or (Bad n) (Fn E (erased (Bad n) q) -> (erased (False) f))) r))
    (match erased (lpo N (level-of dec) E en Bad dec) _
      ((Inl _ _ x) (let-match erased x (MkEx _ m q)) (let-match erased q (MkBad _ g)) (match erased (g m q) _))
      ((Inr _ _ h) (Inl _ _ (MkBad n h)))))
  (def-fns _ $ (many absurd absurd absurdity : -> (many (False) f))
    (match erased (lpo N (level-of dec) E en Bad dec) _
      (absurd (Inl _ _ x) (let-match erased x (MkEx _ n q)) (let-match erased q (MkBad _ g)) (g n q))
      (absurd (Inr _ _ h) (h (Zero) (MkBad (Zero) h)))))
  (values (level-of absurdity) absurdity))
