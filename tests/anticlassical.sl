(def-adts $ (Or : (Type A) (Type B) -> Type)
  enum
  (many Inl : (erased Type A) (erased Type B) (many A a) -> (Or A B))
  (many Inr : (erased Type A) (erased Type B) (many B b) -> (Or A B)))

(def-fns _ $ (many no-lem : (erased (Level) L)
    (erased (Fn L (erased Type P) -> (erased (Or P (Fn L (erased P p) -> (erased (False) f))) d)) lem) ->
    (erased (Level) N) (many (Fn N -> (many (False) f)) absurdity))
  (def-adts $ (Bad : -> Type)
    enum
    (many MkBad : (many (Fn L (erased (Bad) b) -> (erased (False) f)) g) -> (Bad)))
  (def-fns _ $ (erased omega : (many (Bad) b) -> (many (False) f))
    (let-match erased b (MkBad g))
    (g b))
  (def-fns _ $ (many absurd absurdity : -> (many (False) f))
    (match erased (lem (Bad)) _
      (absurd (Inl _ _ b) (omega b))
      (absurd (Inr _ _ n) (omega (MkBad n)))))
  (values (level-of absurdity) absurdity))
