(def-fns _ $ (many attack : (erased (Level) K)
    (erased (Fn K (erased (Level) M) (erased (Level) N) (erased (Predates (Level) M N) mn)
         (erased Type P) (erased (IsProp M P) h) ->
         (erased (Or P (Fn N (erased P p) -> (erased (False) f))) d)) lem) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl M)
  (def-lvl N)
  (let ((erased mn)) (prove-predates M N))
  (def-adts $ (Bad : -> Type)
    enum
    (many MkBad : (erased (Fn N (erased (Bad) b) -> (erased (False) f)) g)
       (erased (Placed vacant-slot (Fn N (erased (Bad) b) -> (erased (False) f)) g) pl) -> (Bad)))
  (def-fns M $ (erased bad-prop : (erased (Bad) x) (erased (Bad) y) -> (erased (Eq (Bad) x y) e))
    (let-match erased x (MkBad g1 p1))
    (let-match erased y (MkBad g2 p2))
    (let ((erased e)) (placed-eq vacant-slot _ g1 p1 p2))
    (match erased e _ ((Refl _ _) (Refl (Bad) x))))
  (values M M))
