; error: `l` was not in scope when level `W` was minted
(def-adts $ (Absurd : -> Type) enum)
(def-adts $ (Bad : -> Type)
  enum
  (many MkBad : (erased (Level) l) (many (Fn l (many (Bad) b) -> (many (Absurd) f)) g) -> (Bad)))
(def-lvl W)
(def-fns W $ (many omega : (many (Bad) b) -> (many (Absurd) f))
  (let-match many b (MkBad l g))
  (g b))
