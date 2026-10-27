(def-adts
  ((NatLe : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many MkNatLe : (erased (Nat) a) (erased (Nat) b) (erased (Lt a (Succ b)) p) -> (NatLe a b))))

(def-fns _ $ (erased le-lt : (erased (Nat) a) (erased (Nat) b) (erased (NatLe a b) p) -> (erased (Lt a (Succ b)) q))
  (let-match erased p (MkNatLe _ _ q))
  q)

(def-fns _ $ (erased lt-pred : (erased (Nat) a) (erased (Nat) b) (erased (Lt (Succ a) (Succ b)) p) -> (erased (Lt a b) q))
  (let-match erased p (LtS _ _ q))
  q)

(def-fns _ $ (erased lt-succ-left : (erased (Nat) a) (erased (Nat) b) (erased (Lt (Succ a) b) p) -> (erased (Lt a b) q))
  (lt-trans a (Succ a) b (lt-succ a) p))

(def-adts
  ((Ne : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many NeLt : (erased (Nat) a) (erased (Nat) b) (erased (Lt a b) p) -> (Ne a b))
    (many NeGt : (erased (Nat) a) (erased (Nat) b) (erased (Lt b a) p) -> (Ne a b))))

(def-fns _ $ (erased lt-irrefl : (erased (Nat) a) (erased (Lt a a) p) -> (erased (False) f))
  (lt-asym a a p (lt-weaken a a p)))

(def-fns _ $ (erased add-le-right : (erased (Nat) a b c) (erased (Add a b c) p) -> (erased (Lt b (Succ c)) q))
  (add-le-left b a c (add-comm a b c p)))

(def-fns _ $ (erased double-le : (erased (Nat) a b) (subterm erased (Double a b) d) -> (erased (Lt a (Succ b)) q))
  (let-match erased d (DS a1 b1 d1) ((D0) (LtZ (Zero))))
  (LtS a1 (Succ (Succ b1)) (lt-weaken a1 (Succ b1) (double-le a1 b1 d1))))
