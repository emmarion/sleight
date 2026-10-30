(def-adts $ (Or : (Type P) (Type Q) -> Type)
  enum
  (many OrL : (erased Type P Q) (erased P p) -> (Or P Q))
  (many OrR : (erased Type P Q) (erased Q q) -> (Or P Q)))

(def-fns _ $ (erased snoc-length : (erased Type A) (erased (List A) xs ys) (erased A a) (erased (Nat) n)
    (subterm erased (Snoc A xs a ys) s) (erased (Length A xs n) l) -> (erased (Length A ys (Succ n)) r))
  (match erased s _
    ((SnocNil _ _) (let-match erased l (LengthNil _)) (LengthCons _ a _ _ (LengthNil _)))
    ((SnocCons _ x _ xs1 ys1 s1)
      (let-match erased l (LengthCons _ _ _ n1 l1))
      (LengthCons _ x ys1 (Succ n1) (snoc-length _ xs1 ys1 a n1 s1 l1)))))

(def-fns _ $ (erased snoc-exists : (erased Type A) (subterm erased (List A) xs) (erased A a) ->
    (erased (List A) ys) (erased (Snoc A xs a ys) s))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values (Cons _ a (Nil _)) (SnocNil _ a))))
  (let ((erased ys1) (erased s1)) (snoc-exists _ xs1 a))
  (values (Cons _ x ys1) (SnocCons _ x a xs1 ys1 s1)))

(def-fns _ $ (erased snoc-old : (erased Type A) (erased (List A) xs ys) (erased A a x) (erased (Nat) i)
    (erased (Snoc A xs a ys) s) (subterm erased (Nth A xs i x) p) -> (erased (Nth A ys i x) q))
  (match erased p _
    ((NthHere _ _ rest) (let-match erased s (SnocCons _ _ _ _ ys1 _)) (NthHere _ x ys1))
    ((NthThere _ y rest i1 _ p1)
      (let-match erased s (SnocCons _ _ _ _ ys1 s1))
      (NthThere _ y ys1 i1 x (snoc-old _ rest ys1 a x i1 s1 p1)))))

(def-fns _ $ (erased snoc-new : (erased Type A) (erased (List A) xs ys) (erased A a) (erased (Nat) n)
    (subterm erased (Snoc A xs a ys) s) (erased (Length A xs n) l) -> (erased (Nth A ys n a) q))
  (match erased s _
    ((SnocNil _ _) (let-match erased l (LengthNil _)) (NthHere _ a (Nil _)))
    ((SnocCons _ x _ xs1 ys1 s1)
      (let-match erased l (LengthCons _ _ _ n1 l1))
      (NthThere _ x ys1 n1 a (snoc-new _ xs1 ys1 a n1 s1 l1)))))

; An entry of the extended list is an old entry or the new one.
(def-fns _ $ (erased snoc-back : (erased Type A) (erased (List A) xs ys) (erased A a x) (erased (Nat) i n)
    (subterm erased (Snoc A xs a ys) s) (erased (Length A xs n) l) (erased (Nth A ys i x) p) ->
    (erased (Or (Nth A xs i x) (Eq (Nat) i n)) r))
  (match erased s _
    ((SnocNil _ _)
      (let-match erased l (LengthNil _))
      (let-match erased p (NthHere _ _ _) (absurd (NthThere _ _ _ _ _ p1) p1))
      (OrR _ _ (Refl _ (Zero))))
    ((SnocCons _ y _ xs1 ys1 s1)
      (let-match erased l (LengthCons _ _ _ n1 l1))
      (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) (OrL _ _ (NthHere _ y xs1))))
      (let-match erased (snoc-back _ xs1 ys1 a x i1 n1 s1 l1 p1) (OrR _ _ e) ((OrL _ _ q) (OrL _ _ (NthThere _ y xs1 i1 x q))))
      (let-match erased e (Refl _ _))
      (OrR _ _ (Refl _ i)))))

(def-fns _ $ (erased insert-at : (erased (List (Nat)) nd nd2) (erased (Nat) d x) (erased (Insert nd d x nd2) p) ->
    (erased (Nth (Nat) nd2 d x) q))
  (let-match erased p (MkInsert _ nd1 _ _ _ c _ s q))
  (snoc-old _ nd1 nd2 c x d q (setnth-nth _ nd d x nd1 s)))

(def-fns _ $ (erased insert-new : (erased (List (Nat)) nd nd2) (erased (Nat) d x n c) (erased (Insert nd d x nd2) p)
    (erased (Length (Nat) nd n) l) (erased (Nth (Nat) nd d c) pc) -> (erased (Nth (Nat) nd2 n c) q))
  (let-match erased p (MkInsert _ nd1 _ _ _ c1 pc1 s q))
  (let-match erased (nth-fn _ nd d c c1 pc pc1) (Refl _ _))
  (snoc-new _ nd1 nd2 c n q (setnth-length _ nd d n x nd1 s l)))

(def-fns _ $ (erased insert-other : (erased (List (Nat)) nd nd2) (erased (Nat) d x i y) (erased (Insert nd d x nd2) p)
    (erased (Nth (Nat) nd i y) pi) (erased (Apart (Nat) Lt i d) ne) -> (erased (Nth (Nat) nd2 i y) q))
  (let-match erased p (MkInsert _ nd1 _ _ _ c _ s q))
  (snoc-old _ nd1 nd2 c y i q
    (match erased ne _
      ((ApLt _ _ _ _ lt) (setnth-nth-lt _ nd d i x y nd1 s pi lt))
      ((ApGt _ _ _ _ gt) (setnth-nth-gt _ nd d i x y nd1 s pi gt)))))

(def-adts $ (InsertBack : ((List (Nat)) nd) ((Nat) d) ((Nat) x) ((Nat) n) ((Nat) i) ((Nat) y) -> Type)
  enum
  (many IBAt : (erased (List (Nat)) nd) (erased (Nat) d x n) -> (InsertBack nd d x n d x))
  (many IBNew : (erased (List (Nat)) nd) (erased (Nat) d x n y) (erased (Nth (Nat) nd d y) p) -> (InsertBack nd d x n n y))
  (many IBOld : (erased (List (Nat)) nd) (erased (Nat) d x n i y) (erased (Nth (Nat) nd i y) p) (erased (Apart (Nat) Lt i d) ne)
      -> (InsertBack nd d x n i y)))

(def-fns _ $ (erased insert-back : (erased (List (Nat)) nd nd2) (erased (Nat) d x n i y) (erased (Insert nd d x nd2) p)
    (erased (Length (Nat) nd n) l) (erased (Nth (Nat) nd2 i y) q) -> (erased (InsertBack nd d x n i y) r))
  (let-match erased p (MkInsert _ nd1 _ _ _ c pc s sn))
  (let-match erased (snoc-back _ nd1 nd2 c y i n sn (setnth-length _ nd d n x nd1 s l) q) (OrL _ _ q1)
    ((OrR _ _ e)
      (let-match erased e (Refl _ _))
      (let-match erased (nth-fn _ nd2 n y c q (snoc-new _ nd1 nd2 c n sn (setnth-length _ nd d n x nd1 s l))) (Refl _ _))
      (IBNew nd d x n y pc)))
  (match erased (nat-cmp i d) _
    ((CLt _ _ _ _ lt) (IBOld nd d x n i y (setnth-back-lt _ nd d i x y nd1 s q1 lt) (ApLt _ _ i d lt)))
    ((CEq _ _ _)
      (let-match erased (nth-fn _ nd1 d y x q1 (setnth-nth _ nd d x nd1 s)) (Refl _ _))
      (IBAt nd d x n))
    ((CGt _ _ _ _ gt) (IBOld nd d x n i y (setnth-back-gt _ nd d i x y nd1 s q1 gt) (ApGt _ _ i d gt)))))
