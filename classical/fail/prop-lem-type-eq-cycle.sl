(def-fns _ $ (erased eq-prop : (erased Type A) (erased A a) (erased A b)
    (erased (Eq A a b) x) (erased (Eq A a b) y) -> (erased (Eq (Eq A a b) x y) e))
  (let-match erased x (Refl _ _))
  (match erased y _ ((Refl _ _) (Refl (Eq A a a) x))))

(def-fns _ $ (many attack : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl M)
  (def-lvl N)
  (let ((erased mn)) (prove-predates M N))
  (def-fns _ $ (erased inner : (erased Type X) (erased X c) -> (erased (False) f))
    (def-adts $ (Pin : -> Type)
      enum
      (many MkPin : (erased c is v) -> (Pin)))
    (def-fns M $ (erased eqp : (erased (Eq Type X (Fn N (erased (Pin) q) -> (erased (False) f))) u)
        (erased (Eq Type X (Fn N (erased (Pin) q) -> (erased (False) f))) w) ->
        (erased (Eq (Eq Type X (Fn N (erased (Pin) q) -> (erased (False) f))) u w) e))
      (eq-prop Type X (Fn N (erased (Pin) q) -> (erased (False) f)) u w))
    (match erased (lem M N mn (Eq Type X (Fn N (erased (Pin) q) -> (erased (False) f)))
                     (MkIsProp M (Eq Type X (Fn N (erased (Pin) q) -> (erased (False) f))) eqp)) _
      (absurd (Inl _ _ e)
        (let-match erased e (Refl _ _))
        (c (MkPin c)))
      (absurd (Inr _ _ n) n)))
  (values (level-of inner) inner))
