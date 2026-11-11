(def-fns _ $ (many attack : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl M)
  (def-lvl N)
  (let ((erased mn)) (prove-predates M N))
  (def-adts $ (Bad : -> Type)
    enum
    (many MkBad : (many (Fn N (erased (Bad) b) -> (erased (False) f)) g) -> (Bad)))
  (def-fns M $ (erased absurd bad-prop : (erased (Bad) x) (erased (Bad) y) -> (erased (Eq (Bad) x y) e))
    (let-match erased x (MkBad g))
    (g x))
  (def-fns _ $ (erased omega : (many (Bad) b) -> (many (False) f))
    (let-match erased b (MkBad g))
    (g b))
  (def-fns _ $ (many absurd absurdity : -> (many (False) f))
    (match erased (lem M N mn (Bad) (MkIsProp M (Bad) bad-prop)) _
      (absurd (Inl _ _ b) (omega b))
      (absurd (Inr _ _ n) (omega (MkBad n)))))
  (values (level-of absurdity) absurdity))
