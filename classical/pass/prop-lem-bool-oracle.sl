(def-adts $ (Reflects : (Type P) ((Bool) b) -> Type)
  enum
  (many RT : (erased Type P) (erased P p) -> (Reflects P (BTrue)))
  (many RF : (erased Type P) (erased (Level) N) (erased (Fn N (erased P p) -> (erased (False) f)) n) -> (Reflects P (BFalse))))

(def-fns _ $ (erased mk : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem) ->
    (erased (Level) O)
    (erased (Fn O (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
      (erased Type P) (erased (IsProp M P) h) -> (erased (Bool) b) (erased (Reflects P b) r)) oracle))
  (def-fns _ $ (erased oracle : (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
      (erased Type P) (erased (IsProp M P) h) -> (erased (Bool) b) (erased (Reflects P b) r))
    (match erased (lem M N mn P h) (((Bool) b) ((Reflects P b) r))
      ((Inl _ _ p) (values (BTrue) (RT P p)))
      ((Inr _ _ n) (values (BFalse) (RF P N n)))))
  (values (level-of oracle) oracle))
