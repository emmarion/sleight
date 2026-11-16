(def-adts $ (Even : ((Nat) n) -> Type)
  enum
  (many EvenZero : -> (Even (Zero)))
  (many EvenStep : (erased (Nat) n) (erased (Even n) p) -> (Even (Succ (Succ n)))))

(def-adts $ (Halves : ((Nat) n) -> Type)
  enum
  (many MkHalves : (erased (Nat) n h) (erased (Double h n) d) -> (Halves n)))

(def-adts $ (Theorem : -> Type)
  enum
  (many MkTheorem : (erased (Level) L) (erased (Fn L (erased (Nat) n) (erased (Even n) p) -> (erased (Halves n) h)) halves) -> (Theorem)))

(goal erased (Theorem))

(def-fns _ $ (erased halves : (erased (Nat) n) (subterm erased (Even n) p) -> (erased (Halves n) h))
  (let-match erased p (EvenStep m q) ((EvenZero) (MkHalves (Zero) (Zero) (D0))))
  (let-match erased (halves m q) (MkHalves _ k d))
  (MkHalves n (Succ k) (DS k m d)))

(qed (MkTheorem (level-of halves) halves))
