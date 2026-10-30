(def-fns _ $ (erased lapp-exists : (erased Type A) (subterm erased (List A) xs) (erased (List A) ys) ->
    (erased (List A) zs) (erased (LApp A xs ys zs) p))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values ys (LAppNil _ ys))))
  (let ((erased zs1) (erased p1)) (lapp-exists _ xs1 ys))
  (values (Cons _ x zs1) (LAppCons _ x xs1 ys zs1 p1)))

(def-fns _ $ (erased lapp-fn : (erased Type A) (erased (List A) xs ys zs zs2) (subterm erased (LApp A xs ys zs) p)
    (erased (LApp A xs ys zs2) q) -> (erased (Eq (List A) zs zs2) e))
  (let-match erased p (LAppCons _ x xs1 _ zs1 p1) ((LAppNil _ _) (let-match erased q (LAppNil _ _)) (Refl _ zs)))
  (let-match erased q (LAppCons _ _ _ _ zs3 q1))
  (let-match erased (lapp-fn _ xs1 ys zs1 zs3 p1 q1) (Refl _ _))
  (Refl _ zs))

(def-fns _ $ (erased lapp-nil : (erased Type A) (subterm erased (List A) xs) -> (erased (LApp A xs (Nil A) xs) p))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (LAppNil _ (Nil _))))
  (LAppCons _ x xs1 (Nil _) xs1 (lapp-nil _ xs1)))

; (a ++ b) ++ c is a ++ (b ++ c).
(def-fns _ $ (erased lapp-assoc : (erased Type A) (erased (List A) a b c ab abc) (subterm erased (LApp A a b ab) p)
    (erased (LApp A ab c abc) q) -> (erased (List A) bc) (erased (LApp A b c bc) r) (erased (LApp A a bc abc) s))
  (let-match erased p (LAppCons _ x a1 _ ab1 p1)
    ((LAppNil _ _) (values abc q (LAppNil _ abc))))
  (let-match erased q (LAppCons _ _ _ _ abc1 q1))
  (let ((erased bc) (erased r) (erased s)) (lapp-assoc _ a1 b c ab1 abc1 p1 q1))
  (values bc r (LAppCons _ x a1 bc abc1 s)))

(def-fns _ $ (erased lapp-assoc-back : (erased Type A) (erased (List A) a b c bc abc) (erased (LApp A b c bc) p)
    (subterm erased (LApp A a bc abc) q) -> (erased (List A) ab) (erased (LApp A a b ab) r) (erased (LApp A ab c abc) s))
  (let-match erased q (LAppCons _ x a1 _ abc1 q1)
    ((LAppNil _ _) (values b (LAppNil _ b) p)))
  (let ((erased ab1) (erased r) (erased s)) (lapp-assoc-back _ a1 b c bc abc1 p q1))
  (values (Cons _ x ab1) (LAppCons _ x a1 b ab1 r) (LAppCons _ x ab1 c abc1 s)))

; Two splits of one list: one cut is before the other.
(def-adts $ (Split2 : (Type A) ((List A) u) ((List A) v) ((List A) b) ((List A) a) -> Type)
  enum
  (many SplitLeft : (erased Type A) (erased (List A) u v b a m) (erased (LApp A u m b) p) (erased (LApp A m a v) q)
      -> (Split2 A u v b a))
  (many SplitRight : (erased Type A) (erased (List A) u v b a m) (erased (LApp A b m u) p) (erased (LApp A m v a) q)
      -> (Split2 A u v b a)))

(def-fns _ $ (erased lapp-split : (erased Type A) (erased (List A) u v b a f) (subterm erased (LApp A u v f) p)
    (erased (LApp A b a f) q) -> (erased (Split2 A u v b a) r))
  (let-match erased p (LAppCons _ x u1 _ f1 p1)
    ((LAppNil _ _) (SplitLeft _ (Nil _) v b a b (LAppNil _ b) q)))
  (let-match erased q (LAppCons _ _ b1 _ _ q1)
    ((LAppNil _ _) (SplitRight _ u v (Nil _) a u (LAppNil _ u) p)))
  (match erased (lapp-split _ u1 v b1 a f1 p1 q1) _
    ((SplitLeft _ _ _ _ _ m p2 q2) (SplitLeft _ u v b a m (LAppCons _ x u1 m b1 p2) q2))
    ((SplitRight _ _ _ _ _ m p2 q2) (SplitRight _ u v b a m (LAppCons _ x b1 m u1 p2) q2))))

; f is a rotation of xs.
(def-adts $ (Rot : (Type A) ((List A) f) ((List A) xs) -> Type)
  enum
  (many MkRot : (erased Type A) (erased (List A) f xs a b) (erased (LApp A a b xs) p) (erased (LApp A b a f) q) -> (Rot A f xs)))

(def-fns _ $ (erased rot-refl : (erased Type A) (erased (List A) xs) -> (erased (Rot A xs xs) r))
  (MkRot _ xs xs (Nil _) xs (LAppNil _ xs) (lapp-nil _ xs)))

; A rotation of a rotation is a rotation.
(def-fns _ $ (erased rot-trans : (erased Type A) (erased (List A) g f xs) (erased (Rot A g f) r1) (erased (Rot A f xs) r2) ->
    (erased (Rot A g xs) r))
  (let-match erased r1 (MkRot _ _ _ u v p1 q1))
  (let-match erased r2 (MkRot _ _ _ a b p2 q2))
  (match erased (lapp-split _ u v b a f p1 q2) _
    ((SplitLeft _ _ _ _ _ m pu pv)
      (let ((erased au) (erased s1) (erased s2)) (lapp-assoc-back _ a u m b xs pu p2))
      (let ((erased au2) (erased s3) (erased s4)) (lapp-assoc _ m a u v g pv q1))
      (let-match erased (lapp-fn _ a u au au2 s1 s3) (Refl _ _))
      (MkRot _ g xs au m s2 s4))
    ((SplitRight _ _ _ _ _ m pu pa)
      (let ((erased vb) (erased s1) (erased s2)) (lapp-assoc _ m v b a xs pa p2))
      (let ((erased vb2) (erased s3) (erased s4)) (lapp-assoc-back _ v b m u g pu q1))
      (let-match erased (lapp-fn _ v b vb vb2 s1 s3) (Refl _ _))
      (MkRot _ g xs m vb s2 s4))))
