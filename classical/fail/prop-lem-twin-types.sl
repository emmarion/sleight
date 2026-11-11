(def-fns _ $ (erased eq-prop : (erased Type A) (erased A a) (erased A b)
    (erased (Eq A a b) x) (erased (Eq A a b) y) -> (erased (Eq (Eq A a b) x y) e))
  (let-match erased x (Refl _ _))
  (match erased y _ ((Refl _ _) (Refl (Eq A a a) x))))

(def-fns _ $ (many attack : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl A)
  (def-lvl B)
  (def-adts $ (BadA : -> Type)
    enum
    (many MkBadA : (many (Fn A (erased (BadA) b) -> (erased (False) f)) g) -> (BadA)))
  (def-adts $ (BadB : -> Type)
    enum
    (many MkBadB : (many (Fn B (erased (BadB) b) -> (erased (False) f)) g) -> (BadB)))
  (def-lvl M)
  (def-lvl N)
  (let ((erased mn)) (prove-predates M N))
  (def-fns M $ (erased eqp : (erased (Eq Type (BadA) (BadB)) u) (erased (Eq Type (BadA) (BadB)) w) ->
      (erased (Eq (Eq Type (BadA) (BadB)) u w) e))
    (eq-prop Type (BadA) (BadB) u w))
  (def-fns _ $ (erased omegaA : (many (BadA) b) -> (many (False) f))
    (let-match erased b (MkBadA g))
    (g b))
  (def-fns _ $ (many absurd absurdity : -> (many (False) f))
    (match erased (lem M N mn (Eq Type (BadA) (BadB)) (MkIsProp M (Eq Type (BadA) (BadB)) eqp)) _
      (absurd (Inl _ _ e)
        (let-match erased e (Refl _ _))
        (def-fns B $ (erased gb : (erased (BadB) b) -> (erased (False) f))
          (omegaA b))
        (omegaA (MkBadA gb)))
      (absurd (Inr _ _ n) n)))
  (values (level-of absurdity) absurdity))
