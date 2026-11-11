(def-adts $ (Unit : ((Nat) n) -> Type)
  enum
  (many tt : (erased (Nat) n) -> (Unit n)))

(def-fns _ $ (many no-wlpo : (erased (Level) B) (erased (Level) K) (erased (Predates (Level) B K) bk)
    (erased (Fn K (erased (Level) N) (erased (Level) W) (erased (Level) D) (erased (Level) E)
        (erased (Predates (Level) E N) en) (erased (Predates (Level) D K) dk)
        (erased (TyCtor ((Nat) n) -> Type) Q)
        (erased (Fn D (erased (Nat) n) -> (erased (Or (Q n) (Fn E (erased (Q n) q) -> (erased (False) f))) r)) dec) ->
        (erased (Or (Fn N (erased (Nat) n) (erased (Q n) q) -> (erased (False) f))
                    (Fn W (erased (Fn N (erased (Nat) n) (erased (Q n) q) -> (erased (False) f)) a) -> (erased (False) f))) r)) wlpo) ->
    (erased (Level) Z) (many (Fn Z -> (many (False) f)) absurdity))
  (def-lvl E)
  (def-lvl W)
  (def-lvl N)
  (let ((erased en)) (prove-predates E N))
  (def-fns B $ (erased dec : (erased (Nat) n) -> (erased (Or (Unit n) (Fn E (erased (Unit n) q) -> (erased (False) f))) r))
    (Inl _ _ (tt n)))
  (def-fns _ $ (many absurd absurd absurdity : -> (many (False) f))
    (match erased (wlpo N N B E en bk Unit dec) _
      (absurd (Inl _ _ all) (all (Zero) (tt (Zero))))
      (absurd (Inr _ _ k)
        (def-fns N $ (erased all : (erased (Nat) n) (erased (Unit n) q) -> (erased (False) f))
          (k all))
        (all (Zero) (tt (Zero))))))
  (values (level-of absurdity) absurdity))
