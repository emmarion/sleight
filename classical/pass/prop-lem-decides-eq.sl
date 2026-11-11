(def-fns _ $ (erased eq-prop : (erased Type A) (erased A a) (erased A b)
    (erased (Eq A a b) x) (erased (Eq A a b) y) -> (erased (Eq (Eq A a b) x y) e))
  (let-match erased x (Refl _ _))
  (match erased y _ ((Refl _ _) (Refl (Eq A a a) x))))
(def-fns _ $ (erased use : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem)
    (erased (Nat) u) (erased (Nat) v) ->
    (erased (Level) N) (erased (Level) Z)
    (erased (Fn Z -> (erased (Or (Eq (Nat) u v) (Fn N (erased (Eq (Nat) u v) p) -> (erased (False) f))) d)) t))
  (def-fns _ $ (erased eq-prop-uv : (erased (Eq (Nat) u v) x) (erased (Eq (Nat) u v) y) ->
      (erased (Eq (Eq (Nat) u v) x y) e))
    (eq-prop (Nat) u v x y))
  (def-lvl N)
  (let ((erased mn)) (prove-predates (level-of eq-prop-uv) N))
  (def-fns _ $ (erased go : -> (erased (Or (Eq (Nat) u v) (Fn N (erased (Eq (Nat) u v) p) -> (erased (False) f))) d))
    (lem (level-of eq-prop-uv) N mn (Eq (Nat) u v) (MkIsProp _ (Eq (Nat) u v) eq-prop-uv)))
  (values N (level-of go) go))
