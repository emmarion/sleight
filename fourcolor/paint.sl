(def-adts $ (PointDec : ((Point) p) ((Point) q) -> Type)
  enum
  (many PtSame : (erased (Point) p) -> (PointDec p p))
  (many PtDiff : (erased (Point) p q) (erased (PointApart p q) d) -> (PointDec p q)))

(def-fns _ $ (many point-dec : (many (Point) p q) -> (many (PointDec p q) r))
  (let-match many p (MkPoint px py))
  (let-match many q (MkPoint qx qy))
  (let-match many (nat-eq px qx) (Equal _ _ _) ((Unequal _ _ _ _ d) (PtDiff p q (ApartX px py qx qy d))))
  (let-match many (nat-eq py qy) (Equal _ _ _) ((Unequal _ _ _ _ d) (PtDiff p q (ApartY px py qx qy d))))
  (PtSame p))

; No paint of ks is at q.
(def-adts $ (Unpainted : ((List (Paint)) ks) ((Point) q) -> Type)
  enum
  (many UnpNil : (erased (Point) q) -> (Unpainted (Nil (Paint)) q))
  (many UnpCons : (erased (List (Paint)) ks) (erased (Point) q r) (erased (Nat) d) (erased (PointApart q r) ap) (erased (Unpainted ks q) u)
      -> (Unpainted (Cons (Paint) (MkPaint r d) ks) q)))

(def-adts $ (PaintLook : ((List (Paint)) ks) ((Point) q) -> Type)
  enum
  (many LookHas : (erased (List (Paint)) ks) (erased (Point) q) (many (Nat) c) (erased (ColorOf ks q c) co) -> (PaintLook ks q))
  (many LookNone : (erased (List (Paint)) ks) (erased (Point) q) (erased (Unpainted ks q) u) -> (PaintLook ks q)))

(def-fns _ $ (many paint-look : (subterm many (List (Paint)) ks) (many (Point) q) -> (many (PaintLook ks q) r))
  (let-match many ks (Cons _ k ks1) ((Nil _) (LookNone ks q (UnpNil q))))
  (let-match many k (MkPaint r d))
  (let-match many (point-dec q r) (PtDiff _ _ ap) ((PtSame _) (LookHas ks q d (ColorHere ks1 q d))))
  (match many (notail $ paint-look ks1 q) _
    ((LookHas _ _ c co) (LookHas ks q c (ColorThere ks1 q r c d ap co)))
    ((LookNone _ _ u) (LookNone ks q (UnpCons ks1 q r d ap u)))))

(def-fns _ $ (erased colorof-unpainted : (erased (List (Paint)) ks) (erased (Point) a q) (erased (Nat) c) (subterm erased (ColorOf ks a c) co)
    (erased (Unpainted ks q) u) -> (erased (PointApart q a) r))
  (let-match erased u (UnpCons ks1 _ _ _ ap u1) (absurd (UnpNil _) co))
  (let-match erased co (ColorThere _ _ _ _ _ _ co1) ((ColorHere _ _ _) ap))
  (colorof-unpainted ks1 a q c co1 u1))

(def-fns _ $ (erased colorof-fn : (erased (List (Paint)) ks) (erased (Point) a) (erased (Nat) c d) (subterm erased (ColorOf ks a c) x)
    (erased (ColorOf ks a d) y) -> (erased (Eq (Nat) c d) e))
  (match erased x _
    ((ColorHere _ _ _)
      (let-match erased y (ColorHere _ _ _) (absurd (ColorThere _ _ _ _ _ ap _) (pa-irrefl a ap)))
      (Refl _ c))
    ((ColorThere ks1 _ _ _ _ ap x1)
      (let-match erased y (ColorThere _ _ _ _ _ _ y1) (absurd (ColorHere _ _ _) (pa-irrefl a ap)))
      (colorof-fn ks1 a c d x1 y1))))

; ks is pre with paints at points unpainted before added in front.
(def-adts $ (Extends : ((List (Paint)) ks pre) -> Type)
  enum
  (many ExtSelf : (erased (List (Paint)) pre) -> (Extends pre pre))
  (many ExtAdd : (erased (List (Paint)) ks pre) (erased (Point) q) (erased (Nat) d) (erased (Extends ks pre) x) (erased (Unpainted ks q) u)
      -> (Extends (Cons (Paint) (MkPaint q d) ks) pre)))

(def-fns _ $ (erased extends-trans : (erased (List (Paint)) ks mid pre) (subterm erased (Extends ks mid) x) (erased (Extends mid pre) y)
    -> (erased (Extends ks pre) r))
  (let-match erased x (ExtAdd ks1 _ q d x1 u) ((ExtSelf _) y))
  (ExtAdd ks1 pre q d (extends-trans ks1 mid pre x1 y) u))

(def-fns _ $ (erased extends-colorof : (erased (List (Paint)) ks pre) (erased (Point) a) (erased (Nat) c) (subterm erased (Extends ks pre) x)
    (erased (ColorOf pre a c) co) -> (erased (ColorOf ks a c) r))
  (let-match erased x (ExtAdd ks1 _ q d x1 u) ((ExtSelf _) co))
  (let ((erased co1)) (extends-colorof ks1 pre a c x1 co))
  (ColorThere ks1 a q c d (apart-point-sym q a (colorof-unpainted ks1 a q c co1 u)) co1))

(def-adts $ (Below4 : ((List (Paint)) ks) -> Type)
  enum
  (many B4Nil : -> (Below4 (Nil (Paint))))
  (many B4Cons : (erased (List (Paint)) ks) (erased (Point) p) (erased (Nat) c) (erased (Lt c 4) l) (erased (Below4 ks) b)
      -> (Below4 (Cons (Paint) (MkPaint p c) ks))))

(def-fns _ $ (erased below4-colorof : (erased (List (Paint)) ks) (erased (Point) a) (erased (Nat) c) (subterm erased (ColorOf ks a c) co)
    (erased (Below4 ks) b) -> (erased (Lt c 4) r))
  (let-match erased b (B4Cons ks1 _ _ l b1) (absurd (B4Nil) co))
  (let-match erased co (ColorThere _ _ _ _ _ _ co1) ((ColorHere _ _ _) l))
  (below4-colorof ks1 a c co1 b1))

(def-adts $ (EndOf : ((Edge) e) ((Point) q) -> Type)
  enum
  (many EndA : (erased (Point) a b) -> (EndOf (MkEdge a b) a))
  (many EndB : (erased (Point) a b) -> (EndOf (MkEdge a b) b)))

; qs are the endpoints of the first edge of todo still to be painted, those before them painted in pre.
(def-adts $ (Pending : ((List (Edge)) todo) ((List (Point)) qs) ((List (Paint)) pre) -> Type)
  enum
  (many PendNil : (erased (List (Point)) qs) (erased (List (Paint)) pre) -> (Pending (Nil (Edge)) qs pre))
  (many PendAB : (erased (Point) a b) (erased (List (Edge)) t) (erased (List (Paint)) pre)
      -> (Pending (Cons (Edge) (MkEdge a b) t) (Cons (Point) a $ Cons (Point) b $ Nil (Point)) pre))
  (many PendB : (erased (Point) a b) (erased (List (Edge)) t) (erased (List (Paint)) pre) (erased (Nat) ca) (erased (ColorOf pre a ca) ka)
      -> (Pending (Cons (Edge) (MkEdge a b) t) (Cons (Point) b $ Nil (Point)) pre))
  (many PendDone : (erased (Point) a b) (erased (List (Edge)) t) (erased (List (Paint)) pre) (erased (Nat) ca cb)
      (erased (ColorOf pre a ca) ka) (erased (ColorOf pre b cb) kb) -> (Pending (Cons (Edge) (MkEdge a b) t) (Nil (Point)) pre)))

(def-fns _ $ (many paint-ends : (erased (List (Paint)) pre) (many (List (Edge)) todo) -> (many (List (Point)) qs) (erased (Pending todo qs pre) pd))
  (let-match many todo (Cons _ e t) ((Nil _) (values (Nil (Point)) (PendNil (Nil (Point)) pre))))
  (let-match many e (MkEdge a b))
  (values (Cons (Point) a $ Cons (Point) b $ Nil (Point)) (PendAB a b t pre)))

(def-fns _ $ (erased pending-next : (erased (List (Edge)) todo) (erased (Point) q) (erased (List (Point)) qs) (erased (List (Paint)) pre pre2)
    (erased (Nat) c) (erased (Pending todo (Cons (Point) q qs) pre) pd) (erased (ColorOf pre2 q c) co) (erased (Extends pre2 pre) x)
    -> (erased (Pending todo qs pre2) r))
  (match erased pd _
    ((PendNil _ _) (PendNil qs pre2))
    ((PendAB a b t _) (PendB a b t pre2 c co))
    ((PendB a b t _ ca ka) (PendDone a b t pre2 ca c (extends-colorof pre2 pre a ca x ka) co))))

(def-fns _ $ (erased pending-end : (erased (Edge) e) (erased (List (Edge)) t) (erased (Point) q) (erased (List (Point)) qs) (erased (List (Paint)) pre)
    (erased (Pending (Cons (Edge) e t) (Cons (Point) q qs) pre) pd) -> (erased (EndOf e q) r))
  (match erased pd _
    ((PendAB a b _ _) (EndA a b))
    ((PendB a b _ _ _ _) (EndB a b))))

; Why no proper four-colouring of todo agrees with pre: two endpoints of the first edge have one colour in pre, or the
; rest fails, or each colour of an endpoint fails.
(def-adts $ (NoPaint : ((List (Edge)) todo) ((List (Paint)) pre) -> Type)
  enum
  (many NPClash : (erased (Point) a b) (erased (List (Edge)) t) (erased (List (Paint)) pre) (erased (Nat) c)
      (erased (ColorOf pre a c) ka) (erased (ColorOf pre b c) kb) -> (NoPaint (Cons (Edge) (MkEdge a b) t) pre))
  (many NPNext : (erased (Point) a b) (erased (List (Edge)) t) (erased (List (Paint)) pre) (erased (Nat) ca cb)
      (erased (ColorOf pre a ca) ka) (erased (ColorOf pre b cb) kb) (erased (NoPaint t pre) n) -> (NoPaint (Cons (Edge) (MkEdge a b) t) pre))
  (many NPFresh : (erased (Edge) e) (erased (List (Edge)) t) (erased (List (Paint)) pre) (erased (Point) q) (erased (EndOf e q) eq)
      (erased (NoPaint (Cons (Edge) e t) (Cons (Paint) (MkPaint q (Zero)) pre)) n0)
      (erased (NoPaint (Cons (Edge) e t) (Cons (Paint) (MkPaint q (Succ (Zero))) pre)) n1)
      (erased (NoPaint (Cons (Edge) e t) (Cons (Paint) (MkPaint q (Succ (Succ (Zero)))) pre)) n2)
      (erased (NoPaint (Cons (Edge) e t) (Cons (Paint) (MkPaint q (Succ (Succ (Succ (Zero))))) pre)) n3)
      -> (NoPaint (Cons (Edge) e t) pre)))

(def-adts $ (PaintSearch : ((List (Edge)) todo) ((List (Paint)) pre) -> Type)
  enum
  (many PaintFound : (erased (List (Edge)) todo) (erased (List (Paint)) pre) (many (List (Paint)) ks) (erased (Extends ks pre) x)
      (erased (Proper ks todo) p) -> (PaintSearch todo pre))
  (many PaintNone : (erased (List (Edge)) todo) (erased (List (Paint)) pre) (erased (NoPaint todo pre) n) -> (PaintSearch todo pre)))

(def-fns _ $ (many paint-go : (subterm many (List (Edge)) todo) (subterm many (List (Point)) qs) (many (List (Paint)) pre) (erased (Below4 pre) bl)
    (erased (Pending todo qs pre) pd) -> (many (PaintSearch todo pre) r))
  (let-match erased (unary-4) (Refl _ _))
  (let-match many todo (Cons _ e t) ((Nil _) (PaintFound todo pre pre (ExtSelf pre) (ProperNil pre))))
  (match many qs _
    ((Cons _ q qs1)
      (let-match many (paint-look pre q) (LookNone _ _ u)
        ((LookHas _ _ c co) (tail $ paint-go todo qs1 pre bl (pending-next todo q qs1 pre pre c pd co (ExtSelf pre)))))
      (let ((erased eq)) (pending-end e t q qs1 pre pd))
      (let ((many p0)) (Cons (Paint) (MkPaint q (Zero)) pre))
      (let ((many p1)) (Cons (Paint) (MkPaint q (Succ (Zero))) pre))
      (let ((many p2)) (Cons (Paint) (MkPaint q (Succ (Succ (Zero)))) pre))
      (let ((many p3)) (Cons (Paint) (MkPaint q (Succ (Succ (Succ (Zero))))) pre))
      (let-match many (notail $ paint-go todo qs1 p0 (B4Cons pre q _ (LtZ _) bl)
          (pending-next todo q qs1 pre p0 _ pd (ColorHere pre q _) (ExtAdd pre pre q _ (ExtSelf pre) u)))
        (PaintNone _ _ n0) ((PaintFound _ _ ks x p) (PaintFound todo pre ks (extends-trans ks p0 pre x (ExtAdd pre pre q _ (ExtSelf pre) u)) p)))
      (let-match many (notail $ paint-go todo qs1 p1 (B4Cons pre q _ (LtS _ _ $ LtZ _) bl)
          (pending-next todo q qs1 pre p1 _ pd (ColorHere pre q _) (ExtAdd pre pre q _ (ExtSelf pre) u)))
        (PaintNone _ _ n1) ((PaintFound _ _ ks x p) (PaintFound todo pre ks (extends-trans ks p1 pre x (ExtAdd pre pre q _ (ExtSelf pre) u)) p)))
      (let-match many (notail $ paint-go todo qs1 p2 (B4Cons pre q _ (LtS _ _ $ LtS _ _ $ LtZ _) bl)
          (pending-next todo q qs1 pre p2 _ pd (ColorHere pre q _) (ExtAdd pre pre q _ (ExtSelf pre) u)))
        (PaintNone _ _ n2) ((PaintFound _ _ ks x p) (PaintFound todo pre ks (extends-trans ks p2 pre x (ExtAdd pre pre q _ (ExtSelf pre) u)) p)))
      (let-match many (notail $ paint-go todo qs1 p3 (B4Cons pre q _ (LtS _ _ $ LtS _ _ $ LtS _ _ $ LtZ _) bl)
          (pending-next todo q qs1 pre p3 _ pd (ColorHere pre q _) (ExtAdd pre pre q _ (ExtSelf pre) u)))
        (PaintNone _ _ n3) ((PaintFound _ _ ks x p) (PaintFound todo pre ks (extends-trans ks p3 pre x (ExtAdd pre pre q _ (ExtSelf pre) u)) p)))
      (PaintNone todo pre (NPFresh e t pre q eq n0 n1 n2 n3)))
    ((Nil _)
      (let-match erased pd (PendDone a b _ _ ca cb ka kb))
      (let-match many e (MkEdge a2 b2))
      (let-match many (paint-look pre a2) (LookHas _ _ ca2 ka2)
        (absurd (LookNone _ _ u) (pa-irrefl a (colorof-unpainted pre a a ca ka u))))
      (let-match many (paint-look pre b2) (LookHas _ _ cb2 kb2)
        (absurd (LookNone _ _ u) (pa-irrefl b (colorof-unpainted pre b b cb kb u))))
      (let-match many (nat-eq ca2 cb2) (Unequal _ _ _ _ ap) ((Equal _ _ _) (PaintNone todo pre (NPClash a b t pre ca2 ka2 kb2))))
      (let ((many qs2) (erased pd2)) (paint-ends pre t))
      (match many (notail $ paint-go t qs2 pre bl pd2) _
        ((PaintNone _ _ n) (PaintNone todo pre (NPNext a b t pre ca2 cb2 ka2 kb2 n)))
        ((PaintFound _ _ ks x p)
          (PaintFound todo pre ks x (ProperCons ks a b ca2 cb2 t (extends-colorof ks pre a ca2 x ka2) (extends-colorof ks pre b cb2 x kb2)
            (below4-colorof pre a ca2 ka2 bl) (below4-colorof pre b cb2 kb2 bl) ap p)))))))

; Every paint of pre is ks's colour of its point.
(def-adts $ (Agrees : ((List (Paint)) pre ks) -> Type)
  enum
  (many AgreeNil : (erased (List (Paint)) ks) -> (Agrees (Nil (Paint)) ks))
  (many AgreeCons : (erased (List (Paint)) pre ks) (erased (Point) p) (erased (Nat) c) (erased (ColorOf ks p c) co) (erased (Agrees pre ks) g)
      -> (Agrees (Cons (Paint) (MkPaint p c) pre) ks)))

(def-fns _ $ (erased agrees-colorof : (erased (List (Paint)) pre ks) (erased (Point) a) (erased (Nat) c) (subterm erased (ColorOf pre a c) co)
    (erased (Agrees pre ks) g) -> (erased (ColorOf ks a c) r))
  (let-match erased g (AgreeCons pre1 _ _ _ k g1) (absurd (AgreeNil _) co))
  (let-match erased co (ColorThere _ _ _ _ _ _ co1) ((ColorHere _ _ _) k))
  (agrees-colorof pre1 ks a c co1 g1))

(def-fns _ $ (erased nopaint-sound : (erased (List (Edge)) todo) (erased (List (Paint)) pre ks) (subterm erased (NoPaint todo pre) n)
    (erased (Agrees pre ks) g) (erased (Proper ks todo) pr) -> (erased (False) f))
  (let-match erased (unary-4) (Refl _ _))
  (match erased n _
    ((NPClash a b _ _ c ka kb)
      (let-match erased pr (ProperCons _ _ _ ca cb _ ka2 kb2 _ _ d _))
      (let-match erased (colorof-fn ks a c ca (agrees-colorof pre ks a c ka g) ka2) (Refl _ _))
      (let-match erased (colorof-fn ks b c cb (agrees-colorof pre ks b c kb g) kb2) (Refl _ _))
      (apart-irrefl c d))
    ((NPNext _ _ t _ _ _ _ _ n1)
      (let-match erased pr (ProperCons _ _ _ _ _ _ _ _ _ _ _ pr1))
      (nopaint-sound t pre ks n1 g pr1))
    ((NPFresh _ _ _ q eq n0 n1 n2 n3)
      (let-match erased pr (ProperCons _ _ _ ca cb _ ka kb la lb _ _))
      (let ((erased c) (erased kq) (erased lq))
        (match erased eq (((Nat) c) ((ColorOf ks q c) kq) ((Lt c 4) lq))
          ((EndA _ _) (values ca ka la))
          ((EndB _ _) (values cb kb lb))))
      (let ((erased g2)) (AgreeCons pre ks q c kq g))
      (let-match erased lq (LtS _ _ l1) ((LtZ _) (nopaint-sound todo _ ks n0 g2 pr)))
      (let-match erased l1 (LtS _ _ l2) ((LtZ _) (nopaint-sound todo _ ks n1 g2 pr)))
      (let-match erased l2 (LtS _ _ l3) ((LtZ _) (nopaint-sound todo _ ks n2 g2 pr)))
      (let-match erased l3 (LtZ _) (absurd (LtS _ _ l4) l4))
      (nopaint-sound todo _ ks n3 g2 pr))))

(def-fns _ $ (many four-color-m : (erased (FourColor) h) -> (erased (Level) L)
    (many (Fn L (many (List (Edge)) es) (erased (Drawing es) drawn) -> (many (List (Paint)) ks) (erased (Proper ks es) proper)) thm))
  (let-match erased h (MkFourColor _ t))
  (def-lvl M)
  (def-fns M $ (many thm : (many (List (Edge)) es) (erased (Drawing es) drawn) -> (many (List (Paint)) ks) (erased (Proper ks es) proper))
    (let ((many qs) (erased pd)) (paint-ends (Nil (Paint)) es))
    (match many (paint-go es qs (Nil (Paint)) (B4Nil) pd) _
      ((PaintFound _ _ ks _ p) (values ks p))
      (absurd (PaintNone _ _ n)
        (let ((erased ks2) (erased p2)) (t es drawn))
        (nopaint-sound es (Nil (Paint)) ks2 n (AgreeNil ks2) p2))))
  (values M thm))
