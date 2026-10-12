(def-adts
  ((Le : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many MkLe : (erased (Nat) a) (erased (Nat) b) (erased (Lt a (Succ b)) p) -> (Le a b))))

(def-fns _ $ (erased le-lt : (erased (Nat) a) (erased (Nat) b) (erased (Le a b) p) -> (erased (Lt a (Succ b)) q))
  (let-match erased p (MkLe _ _ q))
  q)

(def-fns _ $ (erased lt-pred : (erased (Nat) a) (erased (Nat) b) (erased (Lt (Succ a) (Succ b)) p) -> (erased (Lt a b) q))
  (let-match erased p (LtS _ _ q))
  q)

(def-fns _ $ (erased lt-succ-left : (erased (Nat) a) (erased (Nat) b) (erased (Lt (Succ a) b) p) -> (erased (Lt a b) q))
  (lt-trans a (Succ a) b (lt-succ a) p))
