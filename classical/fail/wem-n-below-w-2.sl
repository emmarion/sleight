(def-fns _ $ (many no-wem : (erased (Level) K)
    (erased (Fn K (erased (Level) N) (erased (Level) W) (erased (Predates (Level) N W) nw) (erased Type P) ->
        (erased (Or (Fn N (erased P p) -> (erased (False) f))
                    (Fn W (erased (Fn N (erased P p) -> (erased (False) f)) n) -> (erased (False) f))) r)) wem) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl N)
  (def-lvl W)
  (let ((erased nw)) (prove-predates N W))
  (def-adts $ (P : -> Type)
    enum
    (many MkP : (many (Fn N (erased (P) p) -> (erased (False) f)) x) -> (P)))
  (def-fns _ $ (many absurd absurd absurdity : -> (many (False) f))
    (match erased (wem N W nw (P)) _
      (absurd (Inl _ _ n) (n (MkP n)))
      (absurd (Inr _ _ k)
        (def-fns N $ (erased n : (erased (P) p) -> (erased (False) f))
          (let-match erased p (MkP x))
          (x p))
        (k n))))
  (values (level-of absurdity) absurdity))
