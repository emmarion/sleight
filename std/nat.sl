(def-adts
  ((Le : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many MkLe : (erased (Nat) a) (erased (Nat) b) (erased (Lt a (Succ b)) p) -> (Le a b))))

(def-fns _ $ (erased le-lt : (erased (Nat) a) (erased (Nat) b) (erased (Le a b) p) -> (erased (Lt a (Succ b)) q))
  (let-match erased p (MkLe _ _ q))
  q)
