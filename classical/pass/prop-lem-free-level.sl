(def-fns _ $ (many no-prop-lem-any : (erased (Level) L)
    (erased (Fn L (erased Type P) (erased (Level) M) (erased (IsProp M P) h) ->
       (erased (Or P (Fn L (erased P p) -> (erased (False) f))) d)) lem) ->
    (erased (Level) N) (many (Fn N -> (many (False) f)) absurdity))
  (def-adts $ (Bad : -> Type)
    enum
    (many MkBad : (many (Fn L (erased (Bad) b) -> (erased (False) f)) g) -> (Bad)))
  (def-fns _ $ (erased omega : (many (Bad) b) -> (many (False) f))
    (let-match erased b (MkBad g))
    (g b))
  (def-fns _ $ (erased absurd bad-prop : (erased (Bad) x) (erased (Bad) y) -> (erased (Eq (Bad) x y) e))
    (omega x))
  (def-fns _ $ (many absurd absurdity : -> (many (False) f))
    (match erased (lem (Bad) (level-of bad-prop) (MkIsProp _ (Bad) bad-prop)) _
      (absurd (Inl _ _ b) (omega b))
      (absurd (Inr _ _ n) (omega (MkBad n)))))
  (values (level-of absurdity) absurdity))
