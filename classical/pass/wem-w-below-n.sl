(def-adts $ (Top : -> Type)
  enum
  (many top : -> (Top)))

(def-fns _ $ (many no-wem : (erased (Level) K)
    (erased (Fn K (erased (Level) N) (erased (Level) W) (erased Type P) ->
        (erased (Or (Fn N (erased P p) -> (erased (False) f))
                    (Fn W (erased (Fn N (erased P p) -> (erased (False) f)) n) -> (erased (False) f))) r)) wem) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl W)
  (def-lvl N)
  (def-fns _ $ (many absurd absurd absurdity : -> (many (False) f))
    (match erased (wem N W (Top)) _
      (absurd (Inl _ _ n) (n (top)))
      (absurd (Inr _ _ k)
        (def-fns N $ (erased n : (erased (Top) p) -> (erased (False) f))
          (k n))
        (n (top)))))
  (values (level-of absurdity) absurdity))
