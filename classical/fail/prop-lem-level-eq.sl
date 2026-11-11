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
  (let ((erased ab)) (prove-predates A B))
  (def-adts $ (Bad : -> Type)
    enum
    (many MkBad : (many (Fn A (erased (Bad) b) -> (erased (False) f)) g) -> (Bad)))
  (def-lvl M)
  (def-lvl N)
  (let ((erased mn)) (prove-predates M N))
  (def-fns M $ (erased eqp : (erased (Eq (Level) A B) u) (erased (Eq (Level) A B) w) ->
      (erased (Eq (Eq (Level) A B) u w) e))
    (eq-prop (Level) A B u w))
  (def-fns _ $ (many absurd absurdity : -> (many (False) f))
    (match erased (lem M N mn (Eq (Level) A B) (MkIsProp M (Eq (Level) A B) eqp)) _
      (absurd (Inl _ _ e)
        (let-match erased e (Refl _ _))
        (def-fns A $ (erased omega : (erased (Bad) b) -> (erased (False) f))
          (let-match erased b (MkBad g))
          (g (predates ab) b))
        (omega (MkBad omega)))
      (absurd (Inr _ _ n) n)))
  (values (level-of absurdity) absurdity))
