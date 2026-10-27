(def-fns _ $ (erased ext-pair : (erased (PT) x0 x1) (erased (List (PT)) rest) (erased (List (Tr)) m)
    (erased (Ext (Cons (PT) x0 (Cons (PT) x1 rest)) m) e) ->
    (erased (Tr) t0 t1) (erased (List (Tr)) m2) (erased (Eq (List (Tr)) m (Cons (Tr) t0 (Cons (Tr) t1 m2))) eq) (erased (Ext rest m2) e2))
  (let ((erased t0) (erased m1) (erased e1) (erased eq0))
    (match erased e (((Tr) t0) ((List (Tr)) m1) ((Ext (Cons (PT) x1 rest) m1) e1) ((Eq (List (Tr)) m (Cons (Tr) t0 m1)) eq0))
      ((ExU t0 _ m1 e1) (values t0 m1 e1 (Refl _ m)))
      ((ExD t0 _ m1 e1) (values t0 m1 e1 (Refl _ m)))))
  (let-match erased eq0 (Refl _ _))
  (let ((erased t1) (erased m2) (erased e2) (erased eq))
    (match erased e1 (((Tr) t1) ((List (Tr)) m2) ((Ext rest m2) e2) ((Eq (List (Tr)) m1 (Cons (Tr) t1 m2)) eq))
      ((ExU t1 _ m2 e2) (values t1 m2 e2 (Refl _ m1)))
      ((ExD t1 _ m2 e2) (values t1 m2 e2 (Refl _ m1)))))
  (let-match erased eq (Refl _ _))
  (values t0 t1 m2 (Refl _ m) e2))

(def-fns _ $ (erased ext-tail : (erased (PT) x) (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext (Cons (PT) x p) m) e) ->
    (erased (Tr) t) (erased (List (Tr)) m1) (erased (Eq (List (Tr)) m (Cons (Tr) t m1)) eq) (erased (Ext p m1) e1))
  (match erased e _
    ((ExU t _ m1 e1) (values t m1 (Refl _ m) e1))
    ((ExD t _ m1 e1) (values t m1 (Refl _ m) e1))))

(def-fns _ $ (erased ext-retail : (erased (PT) x) (erased (List (PT)) p p2) (erased (Tr) t) (erased (List (Tr)) m m2)
    (erased (Ext (Cons (PT) x p) (Cons (Tr) t m)) e) (erased (Ext p2 m2) e2) -> (erased (Ext (Cons (PT) x p2) (Cons (Tr) t m2)) e3))
  (match erased e _
    ((ExU _ _ _ _) (ExU t p2 m2 e2))
    ((ExD _ _ _ _) (ExD t p2 m2 e2))))

(def-adts
  ((Swap : ((Nat) a) ((Nat) b) ((Nat) x) ((Nat) y) -> Type)
    enum
    (many SwA : (erased (Nat) a b) -> (Swap a b a b))
    (many SwB : (erased (Nat) a b) -> (Swap a b b a))
    (many SwO : (erased (Nat) a b x) (erased (Apart (Nat) Lt a x) pa) (erased (Apart (Nat) Lt b x) pb) -> (Swap a b x x))))

(def-fns _ $ (erased swap-of : (erased (Nat) a b x) -> (erased (Nat) y) (erased (Swap a b x y) s))
  (let-match erased (nat-eq a x) (Unequal _ _ _ _ pa) ((Equal _ _ _) (values b (SwA a b))))
  (match erased (nat-eq b x) _
    ((Equal _ _ _) (values a (SwB a b)))
    ((Unequal _ _ _ _ pb) (values x (SwO a b x pa pb)))))

(def-fns _ $ (erased swap-same : (erased (Nat) a x y) (erased (Swap a a x y) s) -> (erased (Eq (Nat) y x) e))
  (match erased s _
    ((SwA _ _) (Refl (Nat) y))
    ((SwB _ _) (Refl (Nat) y))
    ((SwO _ _ _ _ _) (Refl (Nat) y))))

(def-fns _ $ (erased swap-below : (erased (Nat) a b x y) (erased (Swap a b x y) s) (erased (Lt x a) la) (erased (Lt x b) lb) -> (erased (Eq (Nat) y x) e))
  (match erased s _
    (absurd (SwA _ _) (apart-irrefl x (ApLt _ _ _ _ la)))
    (absurd (SwB _ _) (apart-irrefl x (ApLt _ _ _ _ lb)))
    ((SwO _ _ _ _ _) (Refl (Nat) y))))

(def-fns _ $ (erased swap-a : (erased (Nat) a b y) (erased (Swap a b a y) s) (erased (Apart (Nat) Lt a b) ab) -> (erased (Eq (Nat) y b) e))
  (match erased s _
    ((SwA _ _) (Refl (Nat) y))
    ((SwB _ _) (Refl (Nat) y))
    (absurd (SwO _ _ _ pa _) (apart-irrefl a pa))))

(def-fns _ $ (erased swap-lt : (erased (Nat) n a b x y) (erased (Swap a b x y) s) (erased (Lt x n) lx) (erased (Lt a n) la) (erased (Lt b n) lb)
    -> (erased (Lt y n) ly))
  (match erased s _ ((SwA _ _) lb) ((SwB _ _) la) ((SwO _ _ _ _ _) lx)))

(def-adts
  ((Flip : ((Bool) f) ((Dir) d) ((Dir) e) -> Type)
    enum
    (many FlN : (erased (Dir) d) -> (Flip (BFalse) d d))
    (many FlL : -> (Flip (BTrue) (DL) (DR)))
    (many FlR : -> (Flip (BTrue) (DR) (DL)))))

(def-fns _ $ (erased flip-of : (erased (Bool) f) (erased (Dir) d) -> (erased (Dir) e) (erased (Flip f d e) fl))
  (let-match erased f (BTrue) ((BFalse) (values d (FlN d))))
  (match erased d _ ((DL) (values (DR) (FlL))) ((DR) (values (DL) (FlR)))))

(def-adts
  ((XT : ((Bool) f) ((Nat) a) ((Nat) b) ((Tr) t) ((Tr) u) -> Type)
    enum
    (many XTH : (erased (Bool) f) (erased (Nat) a b) -> (XT f a b (Halt) (Halt)))
    (many XTG : (erased (Bool) f) (erased (Nat) a b) (erased (Bool) w) (erased (Dir) d e) (erased (Nat) q q2)
       (erased (Flip f d e) fl) (erased (Swap a b q q2) s) -> (XT f a b (Go w d q) (Go w e q2)))))

(def-adts
  ((XM : ((Bool) f) ((Nat) a) ((Nat) b) ((List (Tr)) m) ((List (Tr)) v) -> Type)
    enum
    (many XMNil : (erased (Bool) f) (erased (Nat) a b) -> (XM f a b (Nil (Tr)) (Nil (Tr))))
    (many XMCons : (erased (Bool) f) (erased (Nat) a b) (erased (Tr) t u) (erased (List (Tr)) m v)
       (erased (XT f a b t u) e) (erased (XM f a b m v) r) -> (XM f a b (Cons (Tr) t m) (Cons (Tr) u v)))))

(def-fns _ $ (erased xt-of : (erased (Bool) f) (erased (Nat) a b) (erased (Tr) t) -> (erased (Tr) u) (erased (XT f a b t u) e))
  (let-match erased t (Go w d q) ((Halt) (values (Halt) (XTH f a b))))
  (let ((erased e) (erased fl)) (flip-of f d))
  (let ((erased q2) (erased s)) (swap-of a b q))
  (values (Go w e q2) (XTG f a b w d e q q2 fl s)))

(def-fns _ $ (erased xm-of : (erased (Bool) f) (erased (Nat) a b) (subterm erased (List (Tr)) m) -> (erased (List (Tr)) v) (erased (XM f a b m v) x))
  (let-match erased m (Cons _ t rest) ((Nil _) (values (Nil (Tr)) (XMNil f a b))))
  (let ((erased u) (erased e)) (xt-of f a b t))
  (let ((erased v1) (erased x1)) (xm-of f a b rest))
  (values (Cons (Tr) u v1) (XMCons f a b t u rest v1 e x1)))

(def-fns _ $ (erased xm-pair : (erased (Bool) f) (erased (Nat) a b) (erased (Tr) t0 t1) (erased (List (Tr)) rest v)
    (erased (XM f a b (Cons (Tr) t0 (Cons (Tr) t1 rest)) v) x) ->
    (erased (Tr) u0 u1) (erased (List (Tr)) v1) (erased (XT f a b t0 u0) e0) (erased (XT f a b t1 u1) e1) (erased (XM f a b rest v1) x2)
    (erased (Eq (List (Tr)) v (Cons (Tr) u0 (Cons (Tr) u1 v1))) ev))
  (let-match erased x (XMCons _ _ _ _ u0 _ _ e0 x1))
  (let-match erased x1 (XMCons _ _ _ _ u1 _ v1 e1 x2))
  (values u0 u1 v1 e0 e1 x2 (Refl _ v)))

(def-fns _ $ (erased xt-ok : (erased (Nat) n) (erased (Bool) f) (erased (Nat) a b) (erased (Tr) t u) (erased (TrOK n t) o) (erased (XT f a b t u) e)
    (erased (Lt a n) la) (erased (Lt b n) lb) -> (erased (TrOK n u) o2))
  (let-match erased e (XTG _ _ _ w _ d q q2 _ s) ((XTH _ _ _) (OKHalt n)))
  (let-match erased o (OKGo _ _ _ _ lq))
  (OKGo n q2 w d (swap-lt n a b q q2 s lq la lb)))

(def-fns _ $ (erased xm-rows : (erased (Nat) n k) (erased (Bool) f) (erased (Nat) a b) (erased (List (Tr)) m v) (subterm erased (Rows n k m) w)
    (erased (XM f a b m v) x) (erased (Lt a n) la) (erased (Lt b n) lb) -> (erased (Rows n k v) res))
  (let-match erased w (RowsS _ k1 t0 t1 rest o0 o1 w1) ((RowsZ _) (let-match erased x (XMNil _ _ _)) (RowsZ n)))
  (let ((erased u0) (erased u1) (erased v1) (erased e0) (erased e1) (erased x2) (erased ev)) (xm-pair f a b t0 t1 rest v x))
  (let-match erased ev (Refl _ _))
  (RowsS n k1 u0 u1 v1 (xt-ok n f a b t0 u0 o0 e0 la lb) (xt-ok n f a b t1 u1 o1 e1 la lb) (xm-rows n k1 f a b rest v1 w1 x2 la lb)))

(def-fns _ $ (erased xm-look : (erased (Bool) f) (erased (Nat) a b) (erased (List (Tr)) m v) (erased (Nat) q) (erased (Bool) h) (erased (Tr) t)
    (subterm erased (Look m q h t) lk) (erased (XM f a b m v) x) -> (erased (Tr) u) (erased (XT f a b t u) e) (erased (Look v q h u) lk2))
  (match erased lk _
    ((Look0 t0 t1 rest)
      (let ((erased u0) (erased u1) (erased v1) (erased e0) (erased e1) (erased x2) (erased ev)) (xm-pair f a b t0 t1 rest v x))
      (let-match erased ev (Refl _ _))
      (values u0 e0 (Look0 u0 u1 v1)))
    ((Look1 t0 t1 rest)
      (let ((erased u0) (erased u1) (erased v1) (erased e0) (erased e1) (erased x2) (erased ev)) (xm-pair f a b t0 t1 rest v x))
      (let-match erased ev (Refl _ _))
      (values u1 e1 (Look1 u0 u1 v1)))
    ((LookS t0 t1 rest q1 _ _ lk1)
      (let ((erased u0) (erased u1) (erased v1) (erased e0) (erased e1) (erased x2) (erased ev)) (xm-pair f a b t0 t1 rest v x))
      (let-match erased ev (Refl _ _))
      (let ((erased u) (erased e) (erased lk2)) (xm-look f a b rest v1 q1 h t lk1 x2))
      (values u e (LookS u0 u1 v1 q1 h u lk2)))))

(def-adts
  ((SetRow : ((List (Tr)) m) ((Nat) q) ((Tr) t0) ((Tr) t1) ((List (Tr)) m2) -> Type)
    enum
    (many SR0 : (erased (Tr) x0 x1 t0 t1) (erased (List (Tr)) rest)
       -> (SetRow (Cons (Tr) x0 (Cons (Tr) x1 rest)) (Zero) t0 t1 (Cons (Tr) t0 (Cons (Tr) t1 rest))))
    (many SRS : (erased (Tr) x0 x1 t0 t1) (erased (List (Tr)) rest rest2) (erased (Nat) q) (erased (SetRow rest q t0 t1 rest2) p)
       -> (SetRow (Cons (Tr) x0 (Cons (Tr) x1 rest)) (Succ q) t0 t1 (Cons (Tr) x0 (Cons (Tr) x1 rest2))))))

(def-adts
  ((Sel : ((Bool) h) ((Tr) t0) ((Tr) t1) ((Tr) t) -> Type)
    enum
    (many Sel0 : (erased (Tr) t0 t1) -> (Sel (BFalse) t0 t1 t0))
    (many Sel1 : (erased (Tr) t0 t1) -> (Sel (BTrue) t0 t1 t1))))

(def-fns _ $ (erased sel-of : (erased (Bool) h) (erased (Tr) t0 t1) -> (erased (Tr) t) (erased (Sel h t0 t1 t) sl))
  (match erased h _ ((BFalse) (values t0 (Sel0 t0 t1))) ((BTrue) (values t1 (Sel1 t0 t1)))))

(def-fns _ $ (erased row-look : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) h) (erased (Tr) t0 t1 t)
    (erased (Look m q (BFalse) t0) k0) (erased (Look m q (BTrue) t1) k1x) (erased (Sel h t0 t1 t) sl) -> (erased (Look m q h t) lk))
  (match erased sl _ ((Sel0 _ _) k0) ((Sel1 _ _) k1x)))

(def-fns _ $ (erased row-of : (erased (Nat) n k q) (erased (List (Tr)) m) (subterm erased (Rows n k m) w) (erased (Lt q k) lq) ->
    (erased (Tr) t0 t1) (erased (Look m q (BFalse) t0) k0) (erased (Look m q (BTrue) t1) k1x))
  (let-match erased w (RowsS _ k1 x0 x1 rest _ _ w1) (absurd (RowsZ _) lq))
  (let-match erased q (Succ q1) ((Zero) (values x0 x1 (Look0 x0 x1 rest) (Look1 x0 x1 rest))))
  (let-match erased lq (LtS _ _ lq1))
  (let ((erased t0) (erased t1) (erased k0) (erased k1x)) (row-of n k1 q1 rest w1 lq1))
  (values t0 t1 (LookS x0 x1 rest q1 (BFalse) t0 k0) (LookS x0 x1 rest q1 (BTrue) t1 k1x)))

(def-fns _ $ (erased setrow-of : (erased (Nat) n k q) (erased (List (Tr)) m) (erased (Tr) t0 t1) (subterm erased (Rows n k m) w) (erased (Lt q k) lq) ->
    (erased (List (Tr)) m2) (erased (SetRow m q t0 t1 m2) sr))
  (let-match erased w (RowsS _ k1 x0 x1 rest _ _ w1) (absurd (RowsZ _) lq))
  (let-match erased q (Succ q1) ((Zero) (values (Cons (Tr) t0 (Cons (Tr) t1 rest)) (SR0 x0 x1 t0 t1 rest))))
  (let-match erased lq (LtS _ _ lq1))
  (let ((erased rest2) (erased sr)) (setrow-of n k1 q1 rest t0 t1 w1 lq1))
  (values (Cons (Tr) x0 (Cons (Tr) x1 rest2)) (SRS x0 x1 t0 t1 rest rest2 q1 sr)))

(def-fns _ $ (erased look-set-same : (erased (List (Tr)) m m2) (erased (Nat) q) (erased (Tr) t0 t1 t) (erased (Bool) h)
    (subterm erased (SetRow m q t0 t1 m2) sr) (erased (Sel h t0 t1 t) sl) -> (erased (Look m2 q h t) lk))
  (match erased sr _
    ((SR0 _ _ _ _ rest) (row-look m2 q h t0 t1 t (Look0 t0 t1 rest) (Look1 t0 t1 rest) sl))
    ((SRS x0 x1 _ _ rest rest2 q1 sr1) (LookS x0 x1 rest2 q1 h t (look-set-same rest rest2 q1 t0 t1 t h sr1 sl)))))

(def-fns _ $ (erased look-set-other : (erased (List (Tr)) m m2) (erased (Nat) q q2) (erased (Tr) t0 t1 t) (erased (Bool) h)
    (subterm erased (SetRow m q t0 t1 m2) sr) (erased (Look m q2 h t) lk) (erased (Apart (Nat) Lt q q2) ap) -> (erased (Look m2 q2 h t) lk2))
  (match erased sr _
    ((SR0 _ _ _ _ rest)
      (let-match erased lk (LookS _ _ _ q3 _ _ lk1)
        (absurd (Look0 _ _ _) (apart-irrefl q ap))
        (absurd (Look1 _ _ _) (apart-irrefl q ap)))
      (LookS t0 t1 rest q3 h t lk1))
    ((SRS x0 x1 _ _ rest rest2 q1 sr1)
      (let-match erased lk (LookS _ _ _ q3 _ _ lk1) ((Look0 _ _ _) (Look0 x0 x1 rest2)) ((Look1 _ _ _) (Look1 x0 x1 rest2)))
      (let ((erased ap1))
        (match erased ap (((Apart (Nat) Lt q1 q3) a1))
          ((ApLt _ _ _ _ l) (let-match erased l (LtS _ _ k1x)) (ApLt _ _ q1 q3 k1x))
          ((ApGt _ _ _ _ l) (let-match erased l (LtS _ _ k1x)) (ApGt _ _ q1 q3 k1x))))
      (LookS x0 x1 rest2 q3 h t (look-set-other rest rest2 q1 q3 t0 t1 t h sr1 lk1 ap1)))))

(def-fns _ $ (erased rows-set : (erased (Nat) n k q) (erased (List (Tr)) m m2) (erased (Tr) t0 t1) (subterm erased (SetRow m q t0 t1 m2) sr)
    (erased (Rows n k m) w) (erased (TrOK n t0) o0) (erased (TrOK n t1) o1) -> (erased (Rows n k m2) w2))
  (match erased sr _
    ((SR0 _ _ _ _ rest) (let-match erased w (RowsS _ k1 _ _ _ _ _ w1)) (RowsS n k1 t0 t1 rest o0 o1 w1))
    ((SRS x0 x1 _ _ rest rest2 q1 sr1)
      (let-match erased w (RowsS _ k1 _ _ _ ox0 ox1 w1))
      (RowsS n k1 x0 x1 rest2 ox0 ox1 (rows-set n k1 q1 rest rest2 t0 t1 sr1 w1 o0 o1)))))

(def-adts
  ((PermM : ((Bool) f) ((Nat) a) ((Nat) b) ((List (Tr)) m) ((List (Tr)) v) -> Type)
    enum
    (many PMId : (erased (Bool) f) (erased (Nat) a) (erased (List (Tr)) m m1) (erased (XM f a a m m1) x) -> (PermM f a a m m1))
    (many PMSw : (erased (Bool) f) (erased (Nat) a b) (erased (List (Tr)) m m1 m2 v) (erased (Tr) t0 t1 s0 s1)
       (erased (XM f a b m m1) x) (erased (Apart (Nat) Lt a b) ab)
       (erased (Look m1 a (BFalse) t0) la0) (erased (Look m1 a (BTrue) t1) la1)
       (erased (Look m1 b (BFalse) s0) lb0) (erased (Look m1 b (BTrue) s1) lb1)
       (erased (SetRow m1 a s0 s1 m2) sa) (erased (SetRow m2 b t0 t1 v) sb) -> (PermM f a b m v))))

(def-fns _ $ (erased apart-sym : (erased (Nat) a b) (erased (Apart (Nat) Lt a b) ab) -> (erased (Apart (Nat) Lt b a) ba))
  (match erased ab _ ((ApLt _ _ _ _ l) (ApGt _ _ b a l)) ((ApGt _ _ _ _ l) (ApLt _ _ b a l))))

(def-fns _ $ (erased pm-look : (erased (Bool) f) (erased (Nat) a b) (erased (List (Tr)) m v) (erased (Nat) q q2) (erased (Bool) h) (erased (Tr) t)
    (erased (Look m q h t) lk) (erased (PermM f a b m v) pm) (erased (Swap a b q q2) s) ->
    (erased (Tr) u) (erased (XT f a b t u) e) (erased (Look v q2 h u) lk2))
  (match erased pm _
    ((PMId _ _ _ m1 x)
      (let ((erased u) (erased e) (erased lk1)) (xm-look f a a m m1 q h t lk x))
      (let-match erased (swap-same a q q2 s) (Refl _ _))
      (values u e lk1))
    ((PMSw _ _ _ _ m1 m2 _ t0 t1 s0 s1 x ab la0 la1 lb0 lb1 sa sb)
      (let ((erased u) (erased e) (erased lk1)) (xm-look f a b m m1 q h t lk x))
      (match erased s _
        ((SwA _ _)
          (let ((erased y) (erased sl)) (sel-of h t0 t1))
          (let-match erased (look-fn m1 a h y u (row-look m1 a h t0 t1 y la0 la1 sl) lk1) (Refl _ _))
          (values u e (look-set-same m2 v b t0 t1 y h sb sl)))
        ((SwB _ _)
          (let ((erased y) (erased sl)) (sel-of h s0 s1))
          (let-match erased (look-fn m1 b h y u (row-look m1 b h s0 s1 y lb0 lb1 sl) lk1) (Refl _ _))
          (values u e (look-set-other m2 v b a t0 t1 y h sb (look-set-same m1 m2 a s0 s1 y h sa sl) (apart-sym a b ab))))
        ((SwO _ _ _ pa pb)
          (values u e (look-set-other m2 v b q t0 t1 u h sb (look-set-other m1 m2 a q s0 s1 u h sa lk1 pa) pb)))))))

(def-fns _ $ (erased pm-rows : (erased (Nat) n) (erased (Bool) f) (erased (Nat) a b) (erased (List (Tr)) m v) (erased (Rows n n m) w)
    (erased (PermM f a b m v) pm) (erased (Lt a n) la) (erased (Lt b n) lb) -> (erased (Rows n n v) w2))
  (let-match erased pm (PMSw _ _ _ _ m1 m2 _ t0 t1 s0 s1 x _ la0 la1 lb0 lb1 sa sb) ((PMId _ _ _ m1 x) (xm-rows n n f a a m m1 w x la lb)))
  (let ((erased w1)) (xm-rows n n f a b m m1 w x la lb))
  (let ((erased w2)) (rows-set n n a m1 m2 s0 s1 sa w1 (look-ok n n b m1 (BFalse) s0 w1 lb0) (look-ok n n b m1 (BTrue) s1 w1 lb1)))
  (rows-set n n b m2 v t0 t1 sb w2 (look-ok n n a m1 (BFalse) t0 w1 la0) (look-ok n n a m1 (BTrue) t1 w1 la1)))

(def-adts
  ((FCfg : ((Bool) f) ((List (Bool)) l) ((List (Bool)) r) ((List (Bool)) l2) ((List (Bool)) r2) -> Type)
    enum
    (many FC0 : (erased (List (Bool)) l r) -> (FCfg (BFalse) l r l r))
    (many FC1 : (erased (List (Bool)) l r) -> (FCfg (BTrue) l r r l))))

(def-fns _ $ (erased pm-halts : (erased (Bool) f) (erased (Nat) a b) (erased (List (Tr)) m v) (erased (Nat) q q2) (erased (List (Bool)) l r l2 r2)
    (erased (Bool) h) (erased (Nat) s) (subterm erased (HaltsIn m (MkCfg q l h r) s) hs) (erased (PermM f a b m v) pm)
    (erased (Swap a b q q2) sw) (erased (FCfg f l r l2 r2) fc) -> (erased (HaltsIn v (MkCfg q2 l2 h r2) s) res))
  (match erased hs _
    ((HStop _ _ _ _ _ lk)
      (let ((erased u) (erased e) (erased lk2)) (pm-look f a b m v q q2 h (Halt) lk pm sw))
      (let-match erased e (XTH _ _ _))
      (HStop v q2 l2 r2 h lk2))
    ((HMove _ _ _ s1 st rest)
      (match erased st _
        ((StepL _ _ q3 _ _ k1x _ w h2 lk pp)
          (let ((erased u) (erased e) (erased lk2)) (pm-look f a b m v q q2 h (Go w (DL) q3) lk pm sw))
          (let-match erased e (XTG _ _ _ _ _ _ _ q4 fl s3))
          (match erased fc _
            ((FC0 _ _)
              (let-match erased fl (FlN _))
              (HMove v _ _ s1 (StepL v q2 q4 l r k1x h w h2 lk2 pp)
                (pm-halts f a b m v q3 q4 k1x (Cons (Bool) w r) k1x (Cons (Bool) w r) h2 s1 rest pm s3 (FC0 k1x (Cons (Bool) w r)))))
            ((FC1 _ _)
              (let-match erased fl (FlL))
              (HMove v _ _ s1 (StepR v q2 q4 r l k1x h w h2 lk2 pp)
                (pm-halts f a b m v q3 q4 k1x (Cons (Bool) w r) (Cons (Bool) w r) k1x h2 s1 rest pm s3 (FC1 k1x (Cons (Bool) w r)))))))
        ((StepR _ _ q3 _ _ r1 _ w h2 lk pp)
          (let ((erased u) (erased e) (erased lk2)) (pm-look f a b m v q q2 h (Go w (DR) q3) lk pm sw))
          (let-match erased e (XTG _ _ _ _ _ _ _ q4 fl s3))
          (match erased fc _
            ((FC0 _ _)
              (let-match erased fl (FlN _))
              (HMove v _ _ s1 (StepR v q2 q4 l r r1 h w h2 lk2 pp)
                (pm-halts f a b m v q3 q4 (Cons (Bool) w l) r1 (Cons (Bool) w l) r1 h2 s1 rest pm s3 (FC0 (Cons (Bool) w l) r1))))
            ((FC1 _ _)
              (let-match erased fl (FlR))
              (HMove v _ _ s1 (StepL v q2 q4 r l r1 h w h2 lk2 pp)
                (pm-halts f a b m v q3 q4 (Cons (Bool) w l) r1 r1 (Cons (Bool) w l) h2 s1 rest pm s3 (FC1 (Cons (Bool) w l) r1))))))))))

(def-adts
  ((UList : ((Nat) k) ((List (PT)) p) -> Type)
    enum
    (many UNil : -> (UList (Zero) (Nil (PT))))
    (many UCons : (erased (Nat) k) (erased (List (PT)) p) (erased (UList k p) u) -> (UList (Succ k) (Cons (PT) (Undef) (Cons (PT) (Undef) p))))))

(def-fns _ $ (many undefs : (subterm many (Nat) k) -> (many (List (PT)) p) (erased (UList k p) u))
  (let-match many k (Succ k1) ((Zero) (values (Nil (PT)) (UNil))))
  (let ((many p) (erased u)) (notail $ undefs k1))
  (values (Cons (PT) (Undef) (Cons (PT) (Undef) p)) (UCons k1 p u)))

(def-fns _ $ (erased ext-undef : (erased (Nat) n k) (erased (List (Tr)) m) (erased (List (PT)) p)
    (subterm erased (Rows n k m) rw) (erased (UList k p) u) -> (erased (Ext p m) e))
  (match erased rw _
    ((RowsZ _) (let-match erased u (UNil)) (ExNil))
    ((RowsS _ k1 t0 t1 rest _ _ rw1)
      (let-match erased u (UCons _ p1 u1))
      (ExU t0 (Cons (PT) (Undef) p1) (Cons (Tr) t1 rest) (ExU t1 p1 rest (ext-undef n k1 rest p1 rw1 u1))))))

(def-adts
  ((UF : ((Nat) c) ((List (PT)) p) -> Type)
    enum
    (many UFZ : (erased (Nat) k) (erased (List (PT)) p) (erased (UList k p) u) -> (UF (Zero) p))
    (many UFS : (erased (Nat) c) (erased (PT) x0 x1) (erased (List (PT)) p) (erased (UF c p) u)
       -> (UF (Succ c) (Cons (PT) x0 (Cons (PT) x1 p))))))

(def-adts
  ((Below : ((Nat) c) ((List (PT)) p) -> Type)
    enum
    (many BlwNil : (erased (Nat) c) -> (Below c (Nil (PT))))
    (many BlwU : (erased (Nat) c) (erased (List (PT)) p) (erased (Below c p) r) -> (Below c (Cons (PT) (Undef) p)))
    (many BlwH : (erased (Nat) c) (erased (List (PT)) p) (erased (Below c p) r) -> (Below c (Cons (PT) (Def (Halt)) p)))
    (many BlwG : (erased (Nat) c) (erased (List (PT)) p) (erased (Bool) w) (erased (Dir) d) (erased (Nat) q) (erased (Lt q c) lq)
       (erased (Below c p) r) -> (Below c (Cons (PT) (Def (Go w d q)) p)))))

(def-fns _ $ (erased xm-ext : (erased (Nat) a b c) (erased (List (PT)) p) (erased (List (Tr)) m v) (subterm erased (Ext p m) ex)
    (erased (XM (BFalse) a b m v) x) (erased (Below c p) tb) (erased (Lt c (Succ a)) ca) (erased (Lt c (Succ b)) cb) -> (erased (Ext p v) ex2))
  (match erased ex _
    ((ExNil) (let-match erased x (XMNil _ _ _)) (ExNil))
    ((ExU t p1 m1 ex1)
      (let-match erased x (XMCons _ _ _ _ u _ v1 _ x1))
      (let-match erased tb (BlwU _ _ tb1))
      (ExU u p1 v1 (xm-ext a b c p1 m1 v1 ex1 x1 tb1 ca cb)))
    ((ExD t p1 m1 ex1)
      (let-match erased x (XMCons _ _ _ _ u _ v1 e x1))
      (match erased tb _
        ((BlwH _ _ tb1)
          (let-match erased e (XTH _ _ _))
          (ExD (Halt) p1 v1 (xm-ext a b c p1 m1 v1 ex1 x1 tb1 ca cb)))
        ((BlwG _ _ w d q lq tb1)
          (let-match erased e (XTG _ _ _ _ _ _ _ q2 fl s))
          (let-match erased fl (FlN _))
          (let-match erased (swap-below a b q q2 s (lt-le-trans q c a lq ca) (lt-le-trans q c b lq cb)) (Refl _ _))
          (ExD (Go w d q) p1 v1 (xm-ext a b c p1 m1 v1 ex1 x1 tb1 ca cb)))))))

(def-fns _ $ (erased ext-set-uf : (erased (Nat) c q) (erased (List (PT)) p) (erased (List (Tr)) m m2) (erased (Tr) t0 t1)
    (erased (Ext p m) ex) (subterm erased (SetRow m q t0 t1 m2) sr) (erased (UF c p) uf) (erased (Lt c (Succ q)) cq) -> (erased (Ext p m2) ex2))
  (match erased sr _
    ((SR0 x0 x1 _ _ rest)
      (let-match erased cq (LtZ _) (absurd (LtS _ _ l) l))
      (let-match erased uf (UFZ _ _ u))
      (let-match erased u (UCons _ p1 _) (absurd (UNil) (match erased ex _)))
      (let ((erased a0) (erased a1) (erased mr) (erased eq) (erased e2)) (ext-pair (Undef) (Undef) p1 m ex))
      (let-match erased eq (Refl _ _))
      (ExU t0 (Cons (PT) (Undef) p1) (Cons (Tr) t1 rest) (ExU t1 p1 rest e2)))
    ((SRS x0 x1 _ _ rest rest2 q1 sr1)
      (let ((erased c1) (erased y0) (erased y1) (erased p1) (erased uf1) (erased cq1) (erased ep))
        (match erased uf (((Nat) c1) ((PT) y0) ((PT) y1) ((List (PT)) p1) ((UF c1 p1) uf1) ((Lt c1 (Succ q1)) cq1)
                          ((Eq (List (PT)) p (Cons (PT) y0 (Cons (PT) y1 p1))) ep))
          ((UFZ _ _ u)
            (let-match erased u (UCons k1 p1 u1) (absurd (UNil) (match erased ex _)))
            (values (Zero) (Undef) (Undef) p1 (UFZ k1 p1 u1) (LtZ q1) (Refl _ p)))
          ((UFS c1 y0 y1 p1 uf1) (let-match erased cq (LtS _ _ cq1)) (values c1 y0 y1 p1 uf1 cq1 (Refl _ p)))))
      (let-match erased ep (Refl _ _))
      (let ((erased tA) (erased mA) (erased eqA) (erased eA)) (ext-tail y0 (Cons (PT) y1 p1) m ex))
      (let-match erased eqA (Refl _ _))
      (let ((erased tB) (erased mB) (erased eqB) (erased eB)) (ext-tail y1 p1 mA eA))
      (let-match erased eqB (Refl _ _))
      (let ((erased e3)) (ext-set-uf c1 q1 p1 rest rest2 t0 t1 eB sr1 uf1 cq1))
      (ext-retail y0 (Cons (PT) y1 p1) (Cons (PT) y1 p1) x0 (Cons (Tr) x1 rest) (Cons (Tr) x1 rest2) ex
        (ext-retail y1 p1 p1 x1 rest rest2 eA e3)))))

(def-adts
  ((NextC : ((Nat) n) ((Nat) c) ((Nat) c2) -> Type)
    enum
    (many NCS : (erased (Nat) n c) (erased (Lt c n) l) -> (NextC n c (Succ c)))
    (many NCN : (erased (Nat) n) -> (NextC n n n))))

(def-fns _ $ (erased lt-pos : (erased (Nat) q c) (erased (Lt q c) l) -> (erased (Lt (Zero) c) z))
  (match erased l _ ((LtZ c1) (LtZ c1)) ((LtS _ b _) (LtZ b))))

(def-fns _ $ (erased fit : (erased (Nat) n c c2 q s) (erased (List (Nat)) xs) (erased (List (Tr)) os) (erased (List (PT)) p) (erased (List (Tr)) m)
    (erased (Bool) h) (erased (Tr) tq) (erased (Range c2 xs) rg) (erased (Opts xs os) op) (erased (NextC n c c2) nc) (erased (UF c p) uf)
    (erased (Below c p) bl) (erased (Lt q c) lq) (erased (Ext p m) ex) (erased (Rows n n m) w)
    (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) (erased (Look m q h tq) lk) ->
    (erased (List (Tr)) m2) (erased (Ext p m2) ex2) (erased (Rows n n m2) w2)
    (erased (HaltsIn m2 (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs2) (erased (Tr) tq2) (erased (Look m2 q h tq2) lk2)
    (erased (Mem (Tr) tq2 os) mm) (erased (Nat) a b) (erased (XT (BFalse) a b tq tq2) e))
  (let-match erased (look-ok n n q m h tq w lk) (OKGo _ r wb d lr)
    ((OKHalt _) (values m ex w hs (Halt) lk (opts-halt xs os op) (Zero) (Zero) (XTH (BFalse) (Zero) (Zero)))))
  (let-match erased (lt-dec r c2) (No _ _ _ _ gle)
    ((Yes _ _ _ _ lt)
      (let ((erased y) (erased sw)) (swap-of (Zero) (Zero) r))
      (let-match erased (swap-same (Zero) r y sw) (Refl _ _))
      (values m ex w hs tq lk (opts-go xs os r wb d op (range-mem c2 r xs rg lt)) (Zero) (Zero)
        (XTG (BFalse) (Zero) (Zero) wb d d r r (FlN d) sw))))
  (let ((erased ge)) (lt-eq-succ c2 r gle))
  (let-match erased nc (NCS _ _ lcn) (absurd (NCN _) (lt-asym r n lr ge)))
  (let-match erased ge (LtS _ _ gcr))
  (let ((erased ab)) (ApGt _ _ r c gcr))
  (let ((erased m1) (erased x)) (xm-of (BFalse) r c m))
  (let ((erased w1)) (xm-rows n n (BFalse) r c m m1 w x lr lcn))
  (let ((erased t0) (erased t1) (erased la0) (erased la1)) (row-of n n r m1 w1 lr))
  (let ((erased s0) (erased s1) (erased lb0) (erased lb1)) (row-of n n c m1 w1 lcn))
  (let ((erased m2) (erased sa)) (setrow-of n n r m1 s0 s1 w1 lr))
  (let ((erased w2)) (rows-set n n r m1 m2 s0 s1 sa w1 (look-ok n n c m1 (BFalse) s0 w1 lb0) (look-ok n n c m1 (BTrue) s1 w1 lb1)))
  (let ((erased v) (erased sb)) (setrow-of n n c m2 t0 t1 w2 lcn))
  (let ((erased pm)) (PMSw (BFalse) r c m m1 m2 v t0 t1 s0 s1 x ab la0 la1 lb0 lb1 sa sb))
  (let ((erased lz)) (lt-pos q c lq))
  (let ((erased z) (erased sz)) (swap-of r c (Zero)))
  (let-match erased (swap-below r c (Zero) z sz (lt-trans (Zero) c r lz gcr) lz) (Refl _ _))
  (let ((erased q2) (erased sq)) (swap-of r c q))
  (let-match erased (swap-below r c q q2 sq (lt-trans q c r lq gcr) lq) (Refl _ _))
  (let ((erased u) (erased e) (erased lk2)) (pm-look (BFalse) r c m v q q h tq lk pm sq))
  (let-match erased e (XTG _ _ _ _ _ _ _ r2 fl sr))
  (let-match erased fl (FlN _))
  (let-match erased (swap-a r c r2 sr ab) (Refl _ _))
  (let ((erased lcr)) (lt-weaken c r gcr))
  (let ((erased ex1)) (xm-ext r c c p m m1 ex x bl lcr (lt-succ c)))
  (let ((erased ex2)) (ext-set-uf c r p m1 m2 s0 s1 ex1 sa uf lcr))
  (values v (ext-set-uf c c p m2 v t0 t1 ex2 sb uf (lt-succ c)) (pm-rows n (BFalse) r c m v w pm lr lcn)
    (pm-halts (BFalse) r c m v (Zero) (Zero) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (BFalse) s hs pm sz (FC0 (Nil (Bool)) (Nil (Bool))))
    u lk2 (opts-go xs os c wb d op (range-mem (Succ c) c xs rg (lt-succ c))) r c e))
