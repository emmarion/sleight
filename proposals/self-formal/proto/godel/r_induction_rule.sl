(def-adts $ (All : ((TyCtor ((Nat) n) -> Type) P) -> Type)
  enum
  (many MkAll : (erased (TyCtor ((Nat) n) -> Type) P) (erased (Level) K) (erased (Fn K (subterm erased (Nat) n) -> (erased (P n) p)) f) -> (All P)))
(def-adts $ (Step : ((TyCtor ((Nat) n) -> Type) P) -> Type)
  enum
  (many MkStep : (erased (TyCtor ((Nat) n) -> Type) P) (erased (Level) K) (erased (Fn K (erased (Nat) n) (erased (P n) p) -> (erased (P (Succ n)) q)) f) -> (Step P)))
(def-fns _ $ (erased ind : (erased (TyCtor ((Nat) n) -> Type) P) (erased (P (Zero)) z) (erased (Step P) s) -> (erased (All P) r))
  (let-match erased s (MkStep _ K f))
  (def-lvl N)
  (def-fns N $ (erased go : (subterm erased (Nat) n) -> (erased (P n) p))
    (match erased n _
      ((Zero) z)
      ((Succ m) (f m (go m)))))
  (MkAll P N go))
(def-adts $ (Even : ((Nat) n) -> Type)
  enum
  (many EvenZ : -> (Even (Zero)))
  (many EvenSS : (erased (Nat) n) (erased (Even n) e) -> (Even (Succ (Succ n)))))
(def-adts $ (EvenOr : ((Nat) n) -> Type)
  enum
  (many IsEven : (erased (Nat) n) (erased (Even n) e) -> (EvenOr n))
  (many IsOdd : (erased (Nat) n) (erased (Even (Succ n)) e) -> (EvenOr n)))
(def-fns _ $ (erased step : (erased (Nat) n) (erased (EvenOr n) p) -> (erased (EvenOr (Succ n)) q))
  (match erased p _
    ((IsEven _ e) (IsOdd _ (EvenSS _ e)))
    ((IsOdd _ e) (IsEven _ e))))
(goal erased (All EvenOr))
(qed (ind EvenOr (IsEven _ (EvenZ)) (MkStep EvenOr _ step)))
