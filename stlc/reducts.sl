(def-adts $ (Frame : -> Type)
  enum
  (many FLam : -> (Frame))
  (many FL : (many (Term) a) -> (Frame))
  (many FR : (many (Term) f) -> (Frame)))

(def-adts $ (Plug : ((Frame) fr) ((Term) t) ((Term) u) -> Type)
  enum
  (many PLam : (erased (Term) t) -> (Plug (FLam) t (Lam t)))
  (many PL : (erased (Term) a t) -> (Plug (FL a) t (App t a)))
  (many PR : (erased (Term) f t) -> (Plug (FR f) t (App f t))))

(def-adts $ (MapF : ((Frame) fr) ((List (Term)) xs) ((List (Term)) ys) -> Type)
  enum
  (many MNil : (erased (Frame) fr) -> (MapF fr (Nil (Term)) (Nil (Term))))
  (many MCons : (erased (Frame) fr) (erased (Term) x y) (erased (List (Term)) xs ys) (erased (Plug fr x y) p) (erased (MapF fr xs ys) m)
     -> (MapF fr (Cons (Term) x xs) (Cons (Term) y ys))))

(def-adts $ (Cat : ((List (Term)) xs) ((List (Term)) ys) ((List (Term)) zs) -> Type)
  enum
  (many CNil : (erased (List (Term)) ys) -> (Cat (Nil (Term)) ys ys))
  (many CCons : (erased (Term) x) (erased (List (Term)) xs ys zs) (erased (Cat xs ys zs) c) -> (Cat (Cons (Term) x xs) ys (Cons (Term) x zs))))

(def-adts $ (Beta : ((Term) f) ((Term) a) ((List (Term)) rest) ((List (Term)) ls) -> Type)
  enum
  (many BtLam : (erased (Term) b a r) (erased (List (Term)) rest) (erased (Sub (Zero) a b r) p) -> (Beta (Lam b) a rest (Cons (Term) r rest)))
  (many BtVar : (erased (Nat) i) (erased (Term) a) (erased (List (Term)) rest) -> (Beta (Var i) a rest rest))
  (many BtApp : (erased (Term) f g a) (erased (List (Term)) rest) -> (Beta (App f g) a rest rest)))

(def-adts $ (Reducts : ((Term) t) ((List (Term)) ls) -> Type)
  enum
  (many RVar : (erased (Nat) i) -> (Reducts (Var i) (Nil (Term))))
  (many RLam : (erased (Term) b) (erased (List (Term)) ls ms) (erased (Reducts b ls) r) (erased (MapF (FLam) ls ms) m) -> (Reducts (Lam b) ms))
  (many RApp : (erased (Term) f a) (erased (List (Term)) lf la l1 l2 l3 ls) (erased (Reducts f lf) rf) (erased (Reducts a la) ra)
     (erased (MapF (FL a) lf l1) m1) (erased (MapF (FR f) la l2) m2) (erased (Cat l1 l2 l3) c) (erased (Beta f a l3 ls) bt)
     -> (Reducts (App f a) ls)))

(def-adts $ (AllStep : ((Term) t) ((List (Term)) ls) -> Type)
  enum
  (many ATNil : (erased (Term) t) -> (AllStep t (Nil (Term))))
  (many ATCons : (erased (Term) t x) (erased (List (Term)) xs) (erased (Step t x) p) (erased (AllStep t xs) q) -> (AllStep t (Cons (Term) x xs))))

(def-fns _ $ (erased plug-ex : (erased (Frame) fr) (erased (Term) t) -> (erased (Term) u) (erased (Plug fr t u) p))
  (match erased fr _
    ((FLam) (values (Lam t) (PLam t)))
    ((FL a) (values (App t a) (PL a t)))
    ((FR f) (values (App f t) (PR f t)))))

(def-fns _ $ (erased plug-det : (erased (Frame) fr) (erased (Term) t u1 u2) (erased (Plug fr t u1) p) (erased (Plug fr t u2) q) -> (erased (Eq (Term) u1 u2) e))
  (match erased p _
    ((PLam _) (let-match erased q (PLam _)) (Refl _ u1))
    ((PL _ _) (let-match erased q (PL _ _)) (Refl _ u1))
    ((PR _ _) (let-match erased q (PR _ _)) (Refl _ u1))))

(def-fns _ $ (erased step-plug : (erased (Frame) fr) (erased (Term) t u tt uu) (erased (Step t u) s) (erased (Plug fr t tt) p) (erased (Plug fr u uu) q)
    -> (erased (Step tt uu) r))
  (match erased p _
    ((PLam _) (let-match erased q (PLam _)) (StLam t u s))
    ((PL a _) (let-match erased q (PL _ _)) (StAppL t u a s))
    ((PR f _) (let-match erased q (PR _ _)) (StAppR f t u s))))

(def-fns _ $ (erased map-ex : (erased (Frame) fr) (subterm erased (List (Term)) xs) -> (erased (List (Term)) ys) (erased (MapF fr xs ys) m))
  (let-match erased xs (Cons _ x rest) ((Nil _) (values (Nil _) (MNil fr))))
  (let ((erased y) (erased p)) (plug-ex fr x))
  (let ((erased ys) (erased m)) (map-ex fr rest))
  (values (Cons _ y ys) (MCons fr x y rest ys p m)))

(def-fns _ $ (erased cat-ex : (subterm erased (List (Term)) xs) (erased (List (Term)) ys) -> (erased (List (Term)) zs) (erased (Cat xs ys zs) c))
  (let-match erased xs (Cons _ x rest) ((Nil _) (values ys (CNil ys))))
  (let ((erased zs) (erased c)) (cat-ex rest ys))
  (values (Cons _ x zs) (CCons x rest ys zs c)))

(def-fns _ $ (erased beta-ex : (erased (Term) f a) (erased (List (Term)) rest) -> (erased (List (Term)) ls) (erased (Beta f a rest ls) bt))
  (match erased f _
    ((Var i) (values rest (BtVar i a rest)))
    ((Lam b) (let ((erased r) (erased p)) (sub-ex (Zero) a b)) (values (Cons _ r rest) (BtLam b a r rest p)))
    ((App g h) (values rest (BtApp g h a rest)))))

(def-fns _ $ (erased reducts-ex : (subterm erased (Term) t) -> (erased (List (Term)) ls) (erased (Reducts t ls) r))
  (match erased t _
    ((Var i) (values (Nil _) (RVar i)))
    ((Lam b)
      (let ((erased ls) (erased r)) (reducts-ex b))
      (let ((erased ms) (erased m)) (map-ex (FLam) ls))
      (values ms (RLam b ls ms r m)))
    ((App f a)
      (let ((erased lf) (erased rf)) (reducts-ex f))
      (let ((erased la) (erased ra)) (reducts-ex a))
      (let ((erased l1) (erased m1)) (map-ex (FL a) lf))
      (let ((erased l2) (erased m2)) (map-ex (FR f) la))
      (let ((erased l3) (erased c)) (cat-ex l1 l2))
      (let ((erased ls) (erased bt)) (beta-ex f a l3))
      (values ls (RApp f a lf la l1 l2 l3 ls rf ra m1 m2 c bt)))))

(def-fns _ $ (erased map-sound : (erased (Frame) fr) (erased (Term) t tt) (erased (List (Term)) xs ys) (erased (AllStep t xs) al)
    (subterm erased (MapF fr xs ys) m) (erased (Plug fr t tt) p) -> (erased (AllStep tt ys) q))
  (match erased m _
    ((MNil _) (ATNil tt))
    ((MCons _ x y xs1 ys1 px m1)
      (let-match erased al (ATCons _ _ _ s al1))
      (ATCons tt y ys1 (step-plug fr t x tt y s p px) (map-sound fr t tt xs1 ys1 al1 m1 p)))))

(def-fns _ $ (erased cat-sound : (erased (Term) t) (erased (List (Term)) xs ys zs) (subterm erased (Cat xs ys zs) c)
    (erased (AllStep t xs) a) (erased (AllStep t ys) b) -> (erased (AllStep t zs) d))
  (match erased c _
    ((CNil _) b)
    ((CCons x xs1 _ zs1 c1) (let-match erased a (ATCons _ _ _ s a1)) (ATCons t x zs1 s (cat-sound t xs1 ys zs1 c1 a1 b)))))

(def-fns _ $ (erased reducts-sound : (erased (Term) t) (erased (List (Term)) ls) (subterm erased (Reducts t ls) r) -> (erased (AllStep t ls) a))
  (match erased r _
    ((RVar _) (ATNil t))
    ((RLam b ls1 _ r1 m) (map-sound (FLam) b t ls1 ls (reducts-sound b ls1 r1) m (PLam b)))
    ((RApp f a lf la l1 l2 l3 _ rf ra m1 m2 c bt)
      (let ((erased a3)) (cat-sound t l1 l2 l3 c (map-sound (FL a) f t lf l1 (reducts-sound f lf rf) m1 (PL a f))
                                                 (map-sound (FR f) a t la l2 (reducts-sound a la ra) m2 (PR f a))))
      (match erased bt _
        ((BtLam b _ x _ p) (ATCons t x l3 (StBeta b a x p) a3))
        ((BtVar _ _ _) a3)
        ((BtApp _ _ _ _) a3)))))

(def-fns _ $ (erased mem-map : (erased (Frame) fr) (erased (List (Term)) xs ys) (erased (Nat) i) (erased (Term) x y)
    (subterm erased (Nth (Term) xs i x) n) (erased (MapF fr xs ys) m) (erased (Plug fr x y) p) -> (erased (Nth (Term) ys i y) q))
  (match erased n _
    ((NthHere _ _ _)
      (let-match erased m (MCons _ _ y1 _ ys1 p1 _))
      (let-match erased (plug-det fr x y1 y p1 p) (Refl _ _))
      (NthHere _ y ys1))
    ((NthThere _ _ xs1 i1 _ n1)
      (let-match erased m (MCons _ _ y1 _ ys1 _ m1))
      (NthThere _ y1 ys1 i1 y (mem-map fr xs1 ys1 i1 x y n1 m1 p)))))

(def-fns _ $ (erased mem-cat-l : (erased (List (Term)) xs ys zs) (erased (Nat) i) (erased (Term) x)
    (subterm erased (Nth (Term) xs i x) n) (erased (Cat xs ys zs) c) -> (erased (Nth (Term) zs i x) q))
  (match erased n _
    ((NthHere _ _ _) (let-match erased c (CCons _ _ _ zs1 _)) (NthHere _ x zs1))
    ((NthThere _ y xs1 i1 _ n1) (let-match erased c (CCons _ _ _ zs1 c1)) (NthThere _ y zs1 i1 x (mem-cat-l xs1 ys zs1 i1 x n1 c1)))))

(def-fns _ $ (erased mem-cat-r : (erased (List (Term)) xs ys zs) (erased (Nat) i) (erased (Term) x)
    (erased (Nth (Term) ys i x) n) (subterm erased (Cat xs ys zs) c) -> (erased (Nat) k) (erased (Nth (Term) zs k x) q))
  (match erased c _
    ((CNil _) (values i n))
    ((CCons y xs1 _ zs1 c1)
      (let ((erased k) (erased q)) (mem-cat-r xs1 ys zs1 i x n c1))
      (values (Succ k) (NthThere _ y zs1 k x q)))))

(def-fns _ $ (erased mem-beta : (erased (Term) f a) (erased (List (Term)) rest ls) (erased (Nat) i) (erased (Term) x)
    (erased (Nth (Term) rest i x) n) (erased (Beta f a rest ls) bt) -> (erased (Nat) k) (erased (Nth (Term) ls k x) q))
  (match erased bt _
    ((BtLam _ _ r _ _) (values (Succ i) (NthThere _ r rest i x n)))
    ((BtVar _ _ _) (values i n))
    ((BtApp _ _ _ _) (values i n))))

(def-fns _ $ (erased reducts-complete : (erased (Term) t u) (erased (List (Term)) ls) (subterm erased (Reducts t ls) r) (erased (Step t u) s)
    -> (erased (Nat) i) (erased (Nth (Term) ls i u) n))
  (match erased s _
    ((StBeta b a _ p)
      (let-match erased r (RApp _ _ _ _ _ _ l3 _ _ _ _ _ _ bt))
      (let-match erased bt (BtLam _ _ x _ q))
      (let-match erased (sub-det (Zero) a b u x p q) (Refl _ _))
      (values (Zero) (NthHere _ u l3)))
    ((StLam b c s1)
      (let-match erased r (RLam _ ls1 _ r1 m))
      (let ((erased i) (erased n)) (reducts-complete b c ls1 r1 s1))
      (values i (mem-map (FLam) ls1 ls i c u n m (PLam c))))
    ((StAppL f g a s1)
      (let-match erased r (RApp _ _ lf la l1 l2 l3 _ rf _ m1 _ c bt))
      (let ((erased i) (erased n)) (reducts-complete f g lf rf s1))
      (mem-beta f a l3 ls i u (mem-cat-l l1 l2 l3 i u (mem-map (FL a) lf l1 i g u n m1 (PL a g)) c) bt))
    ((StAppR f a b s1)
      (let-match erased r (RApp _ _ lf la l1 l2 l3 _ _ ra _ m2 c bt))
      (let ((erased i) (erased n)) (reducts-complete a b la ra s1))
      (let ((erased k) (erased n2)) (mem-cat-r l1 l2 l3 i u (mem-map (FR f) la l2 i b u n m2 (PR f b)) c))
      (mem-beta f a l3 ls k u n2 bt))))

(def-adts
  ((Sn : ((Term) t) -> Type)
    enum
    (many MkSn : (erased (Term) t) (erased (List (Term)) ls) (erased (Reducts t ls) r) (erased (AllSn ls) a) -> (Sn t)))
  ((AllSn : ((List (Term)) ls) -> Type)
    enum
    (many ASNil : -> (AllSn (Nil (Term))))
    (many ASCons : (erased (Term) x) (erased (List (Term)) xs) (erased (Sn x) d) (erased (AllSn xs) a) -> (AllSn (Cons (Term) x xs)))))

(def-fns _ $ (erased allsn-get : (erased (List (Term)) ls) (subterm erased (AllSn ls) d) (erased (Nat) i) (erased (Term) x) (erased (Nth (Term) ls i x) n)
    -> (erased (Sn x) e) (erased (Subterm (Sn x) e (AllSn ls) d) p))
  (match erased n _
    ((NthHere _ _ _) (let-match erased d (ASCons _ _ dx _)) (values dx (prove-subterm dx d)))
    ((NthThere _ _ xs i1 _ n1)
      (let-match erased d (ASCons _ _ _ d1))
      (let ((erased e) (erased p)) (allsn-get xs d1 i1 x n1))
      (values e (subterm-trans p (prove-subterm d1 d))))))

(def-fns _ $ (erased sn-step : (erased (Term) t u) (erased (Sn t) d) (erased (Step t u) s) -> (erased (Sn u) e) (erased (Subterm (Sn u) e (Sn t) d) p))
  (let-match erased d (MkSn _ ls r a))
  (let ((erased i) (erased n)) (reducts-complete t u ls r s))
  (let ((erased e) (erased p)) (allsn-get ls a i u n))
  (values e (subterm-trans p (prove-subterm a d))))
