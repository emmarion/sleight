(def-adts $ (Or : (Type P) (Type Q) -> Type)
  enum
  (many OrL : (erased Type P Q) (erased P p) -> (Or P Q))
  (many OrR : (erased Type P Q) (erased Q q) -> (Or P Q)))

(def-adts $ (NotIn : ((Nat) x) ((List (Nat)) s) -> Type)
  enum
  (many NotInNil : (erased (Nat) x) -> (NotIn x (Nil (Nat))))
  (many NotInCons : (erased (Nat) x y) (erased (List (Nat)) s) (erased (Apart (Nat) Lt x y) ne) (erased (NotIn x s) rest)
      -> (NotIn x (Cons (Nat) y s))))

(def-adts $ (In : ((Nat) x) ((List (Nat)) s) -> Type)
  enum
  (many InHere : (erased (Nat) x) (erased (List (Nat)) s) -> (In x (Cons (Nat) x s)))
  (many InThere : (erased (Nat) x y) (erased (List (Nat)) s) (erased (In x s) p) -> (In x (Cons (Nat) y s))))

(def-fns _ $ (erased notin-in : (erased (Nat) x y) (erased (List (Nat)) s) (subterm erased (NotIn x s) p) (erased (In y s) q) ->
    (erased (Apart (Nat) Lt x y) ne))
  (let-match erased p (NotInCons _ z s1 ne1 p1) (absurd (NotInNil _) q))
  (let-match erased q (InThere _ _ _ q1) ((InHere _ _) ne1))
  (notin-in x y s1 p1 q1))

(def-adts $ (Distinct : ((List (Nat)) s) -> Type)
  enum
  (many DistNil : -> (Distinct (Nil (Nat))))
  (many DistCons : (erased (Nat) x) (erased (List (Nat)) s) (erased (NotIn x s) p) (erased (Distinct s) rest)
      -> (Distinct (Cons (Nat) x s))))

