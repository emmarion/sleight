; error: `W` was not in scope when level `(level-of knot)` was minted
(def-adts $ (Absurd : -> Type) enum)
(def-adts $ (Bad : -> Type)
  enum
  (many MkBad : (erased (Level) l) (many (Fn l (many (Bad) b) -> (many (Absurd) f)) g) -> (Bad)))
(def-fns _ $ (many factory : (many (Bad) b) ->
    (erased (Level) W) (many (Fn W -> (many (Absurd) f)) o))
  (def-lvl W)
  (let ((erased pb)) (prove-predates b W))
  (let-match many b (MkBad l g))
  (let ((erased ps)) (prove-subterm l b))
  (let ((erased pl)) (predates-subterm pb ps))
  (def-fns W $ (many o : -> (many (Absurd) f))
    (g (predates pl) b))
  (values W o))
(def-fns _ $ (many knot : (many (Bad) b) -> (many (Absurd) f))
  (let ((erased W) (many o)) (factory b))
  (o))
