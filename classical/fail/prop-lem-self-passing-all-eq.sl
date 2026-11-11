(def-fns _ $ (many attack : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl M)
  (let ((erased km)) (prove-predates K M))
  (def-lvl N0)
  (let ((erased mn0)) (prove-predates M N0))
  (def-lvl N)
  (let ((erased n0n)) (prove-predates N0 N))
  (let ((erased kn)) (prove-predates K N))
  (let ((erased mn)) (prove-predates M N))
  (def-adts $ (Bad : -> Type)
    enum
    (many MkBad : (many (Fn N (erased (Bad) b) -> (erased (False) f)) g) -> (Bad)))
  (def-fns M $ (erased bad-prop : (erased (Bad) x) (erased (Bad) y) -> (erased (Eq (Bad) x y) e))
    (def-fns N $ (erased g2 : (erased (Bad) b) -> (erased (False) f))
      (match erased (lem (predates kn) M N0 mn0 (Bad) (MkIsProp M (Bad) bad-prop)) _
        (absurd (Inl _ _ b2) (let-match erased b2 (MkBad g3)) (g3 b2))
        (absurd (Inr _ _ n0) (n0 (predates n0n) b))))
    (match erased (lem (predates km) M N0 mn0 (Bad) (MkIsProp M (Bad) bad-prop)) _
      (absurd (Inl _ _ b2) (let-match erased b2 (MkBad g3)) (g3 b2))
      (absurd (Inr _ _ n0) (n0 x))))
  (def-fns _ $ (erased omega : (many (Bad) b) -> (many (False) f))
    (let-match erased b (MkBad g))
    (g b))
  (def-fns _ $ (many absurd absurdity : -> (many (False) f))
    (match erased (lem M N mn (Bad) (MkIsProp M (Bad) bad-prop)) _
      (absurd (Inl _ _ b) (omega b))
      (absurd (Inr _ _ n) (omega (MkBad n)))))
  (values (level-of absurdity) absurdity))
