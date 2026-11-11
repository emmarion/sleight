(def-fns _ $ (many attack-lowG : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl G)
  (def-adts $ (Bad : -> Type)
    enum
    (many MkBad : (many (Fn G (erased (Bad) b) -> (erased (False) f)) g) -> (Bad)))
  (def-fns _ $ (erased omega : (many (Bad) b) -> (many (False) f))
    (let-match erased b (MkBad g))
    (g b))
  (def-fns _ $ (erased absurd bad-prop : (erased (Bad) x) (erased (Bad) y) -> (erased (Eq (Bad) x y) e))
    (omega x))
  (def-lvl N)
  (let ((erased mn)) (prove-predates (level-of bad-prop) N))
  (def-fns _ $ (many absurd absurdity : -> (many (False) f))
    (match erased (lem (level-of bad-prop) N mn (Bad) (MkIsProp _ (Bad) bad-prop)) _
      (absurd (Inl _ _ b) (omega b))
      (absurd (Inr _ _ n) (omega (MkBad n)))))
  (values (level-of absurdity) absurdity))
