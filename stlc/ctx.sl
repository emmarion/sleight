(def-adts $ (Ins : ((Nat) k) ((Ty) a) ((List (Ty)) g) ((List (Ty)) h) -> Type)
  enum
  (many InsZ : (erased (Ty) a) (erased (List (Ty)) g) -> (Ins (Zero) a g (Cons (Ty) a g)))
  (many InsS : (erased (Nat) k) (erased (Ty) a b) (erased (List (Ty)) g h) (erased (Ins k a g h) p)
     -> (Ins (Succ k) a (Cons (Ty) b g) (Cons (Ty) b h))))

(def-fns _ $ (erased ins-hit : (erased (Nat) k) (erased (Ty) a) (erased (List (Ty)) g h) (subterm erased (Ins k a g h) p) -> (erased (Nth (Ty) h k a) q))
  (match erased p _
    ((InsZ _ _) (NthHere _ a g))
    ((InsS k1 _ b g1 h1 p1) (NthThere _ b h1 k1 a (ins-hit k1 a g1 h1 p1)))))

(def-fns _ $ (erased ins-fwd : (erased (Nat) k) (erased (Ty) a) (erased (List (Ty)) g h) (subterm erased (Ins k a g h) p)
    (erased (Nat) i j) (erased (Skip k i j) s) (erased (Ty) c) (erased (Nth (Ty) g i c) n) -> (erased (Nth (Ty) h j c) m))
  (match erased p _
    ((InsZ _ _) (let-match erased s (SkipZ _)) (NthThere _ a g i c n))
    ((InsS k1 _ b g1 h1 p1)
      (match erased s _
        ((SkipLo _) (let-match erased n (NthHere _ _ _)) (NthHere _ b h1))
        ((SkipHi _ i1 j1 s1)
          (let-match erased n (NthThere _ _ _ _ _ n1))
          (NthThere _ b h1 j1 c (ins-fwd k1 a g1 h1 p1 i1 j1 s1 c n1)))))))

(def-fns _ $ (erased ins-back : (erased (Nat) k) (erased (Ty) a) (erased (List (Ty)) g h) (subterm erased (Ins k a g h) p)
    (erased (Nat) i j) (erased (Skip k i j) s) (erased (Ty) c) (erased (Nth (Ty) h j c) n) -> (erased (Nth (Ty) g i c) m))
  (match erased p _
    ((InsZ _ _) (let-match erased s (SkipZ _)) (let-match erased n (NthThere _ _ _ _ _ n1)) n1)
    ((InsS k1 _ b g1 h1 p1)
      (match erased s _
        ((SkipLo _) (let-match erased n (NthHere _ _ _)) (NthHere _ b g1))
        ((SkipHi _ i1 j1 s1)
          (let-match erased n (NthThere _ _ _ _ _ n1))
          (NthThere _ b g1 i1 c (ins-back k1 a g1 h1 p1 i1 j1 s1 c n1)))))))

(def-fns _ $ (erased nth-det : (erased (List (Ty)) g) (erased (Nat) i) (erased (Ty) a b) (subterm erased (Nth (Ty) g i a) p) (erased (Nth (Ty) g i b) q)
    -> (erased (Eq (Ty) a b) e))
  (match erased p _
    ((NthHere _ _ _) (let-match erased q (NthHere _ _ _)) (Refl _ a))
    ((NthThere _ _ g1 i1 _ p1) (let-match erased q (NthThere _ _ _ _ _ q1)) (nth-det g1 i1 a b p1 q1))))
