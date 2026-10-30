; A certified redpart after redpart.v, on the named darts of rdart.sl: RedD qt p is evidence that every dart fitting
; the part p exactly makes the quiz tree qt fit at some dart (red-sound), the contrapositive of no_fit_redpart. Load
; after rdart.sl.

(def-adts $ (RNs : ((List (Sub)) p) ((RDart) t u) -> Type)
  enum
  (many MkRNs : (erased (List (Sub)) p) (erased (RDart) t t1 u) (erased (RFi t t1) s) (erased (REst p t1 u) r) -> (RNs p t u)))

(def-adts $ (RQr : ((List (Sub)) p) ((RDart) t u) -> Type)
  enum
  (many MkRQr : (erased (List (Sub)) p) (erased (RDart) t a b u) (erased (REst p t a) r1) (erased (RFi a b) s) (erased (REst p b u) r2)
      -> (RQr p t u)))

(def-adts $ (RQl : ((List (Sub)) p) ((RDart) t u) -> Type)
  enum
  (many MkRQl : (erased (List (Sub)) p) (erased (RDart) t a b u) (erased (RFi t a) s1) (erased (RFi a b) s2) (erased (REst p b u) r)
      -> (RQl p t u)))

(def-fns _ $ (erased rns-sound : (erased (Nat) d x0 y) (erased (List (Nat)) e n f ks) (erased (List (Sub)) p) (erased (Geo d e n f ks) g)
    (erased (ExactAt e f ks x0 p) ex) (erased (RDart) t u) (erased (RNs p t u) r) (erased (RSem e f x0 t y) s) (erased (Lt y d) ly)
    -> (erased (Nat) z) (erased (Nth (Nat) n y z) pz) (erased (RSem e f x0 u z) q) (erased (Lt z d) lz))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core d e n f h))
  (let-match erased r (MkRNs _ _ t1 _ s1 r1))
  (let ((erased y1) (erased p1) (erased l1)) (f-pre d y e n f h ly))
  (let ((erased z) (erased pz) (erased lz)) (perm-nth d y1 e nf qe l1))
  (values z (n-ef d y1 y z e n f ks g l1 p1 pz) (rest-sound d x0 y1 z e n f ks p g ex t1 u r1 (rfi-sound d e f fi qf x0 y y1 t t1 s p1 s1) l1 pz) lz))

(def-fns _ $ (erased rqr-sound : (erased (Nat) d x0 y) (erased (List (Nat)) e n f ks) (erased (List (Sub)) p) (erased (Geo d e n f ks) g)
    (erased (ExactAt e f ks x0 p) ex) (erased (RDart) t u) (erased (RQr p t u) r) (erased (RSem e f x0 t y) s) (erased (Lt y d) ly)
    -> (erased (Nat) z) (erased (QStepR e n y z) pz) (erased (RSem e f x0 u z) q) (erased (Lt z d) lz))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core d e n f h))
  (let-match erased r (MkRQr _ _ a b _ r1 s1 r2))
  (let ((erased ya) (erased pa) (erased la)) (perm-nth d y e nf qe ly))
  (let ((erased sa)) (rest-sound d x0 y ya e n f ks p g ex t a r1 s ly pa))
  (let ((erased yb) (erased pb) (erased lb)) (f-pre d ya e n f h la))
  (let ((erased z) (erased pz) (erased lz)) (perm-nth d yb e nf qe lb))
  (values z (MkQStepR e n y ya z pa (n-ef d yb ya z e n f ks g lb pb pz))
    (rest-sound d x0 yb z e n f ks p g ex b u r2 (rfi-sound d e f fi qf x0 ya yb a b sa pb s1) lb pz) lz))

(def-fns _ $ (erased rql-sound : (erased (Nat) d x0 y) (erased (List (Nat)) e n f ks) (erased (List (Sub)) p) (erased (Geo d e n f ks) g)
    (erased (ExactAt e f ks x0 p) ex) (erased (RDart) t u) (erased (RQl p t u) r) (erased (RSem e f x0 t y) s) (erased (Lt y d) ly)
    -> (erased (Nat) z) (erased (QStepL e n y z) pz) (erased (RSem e f x0 u z) q) (erased (Lt z d) lz))
  (let-match erased g (MkGeo _ _ _ _ _ h pl _ _ _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core d e n f h))
  (let-match erased r (MkRQl _ _ a b _ s1 s2 r1))
  (let ((erased ya) (erased pa) (erased la)) (f-pre d y e n f h ly))
  (let ((erased yb) (erased pb) (erased lb)) (f-pre d ya e n f h la))
  (let ((erased c) (erased pc) (erased _)) (perm-nth d ya e nf qe la))
  (let ((erased z) (erased pz) (erased lz)) (perm-nth d yb e nf qe lb))
  (let ((erased pc2) (erased _)) (plain-eq d ya c e pl la pc))
  (let ((erased sb)) (rfi-sound d e f fi qf x0 ya yb a b (rfi-sound d e f fi qf x0 y ya t a s pa s1) pb s2))
  (values z (MkQStepL e n y c ya z (n-ef d ya y c e n f ks g la pa pc) pc2 (n-ef d yb ya z e n f ks g lb pb pz))
    (rest-sound d x0 yb z e n f ks p g ex b u r1 sb lb pz) lz))

(def-adts $ (RFaceOf : ((RDart) t) ((RFace) i) -> Type)
  enum
  (many FOF : (erased (RFace) i) (erased (Nat) k) -> (RFaceOf (DF i k) i))
  (many FOB : (erased (RFace) i) (erased (Nat) k) -> (RFaceOf (DB i k) i)))

(def-fns _ $ (erased rsem-base : (erased (Nat) d x0 y) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (RDart) t) (erased (RFace) i)
    (erased (RSem e f x0 t y) s) (erased (RFaceOf t i) fo) (erased (Lt y d) ly)
    -> (erased (Nat) b c) (erased (RBase e f x0 i b) bb) (erased (Lt b d) lb) (erased (Nth (Nat) ks b c) pb) (erased (Nth (Nat) ks y c) py))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ ol _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core d e n f h))
  (let ((erased c) (erased py) (erased _)) (arity-at d y f ks ol ly))
  (match erased fo _
    ((FOF _ k)
      (let-match erased s (RSF _ _ _ _ b _ _ bb it))
      (let ((erased lb)) (iter-lt-inv d k b y f fi qf ly it))
      (let ((erased c2) (erased pb) (erased _)) (arity-at d b f ks ol lb))
      (let-match erased (arity-same d b y k c2 c e n f ks g lb pb it py) (Refl _ _))
      (values b c bb lb pb py))
    ((FOB _ k)
      (let-match erased s (RSB _ _ _ _ b _ _ bb it))
      (let ((erased lb)) (iter-lt d k y b f fi qf ly it))
      (let ((erased c2) (erased pb) (erased _)) (arity-at d b f ks ol lb))
      (let-match erased (arity-same d y b k c c2 e n f ks g ly py it pb) (Refl _ _))
      (values b c bb lb pb py))))

(def-adts $ (RPop : -> Type)
  enum
  (many MkRPop : (many (List (Sub)) p) (many (Nat) s) -> (RPop)))

(def-adts $ (PopHit : ((List (Nat)) e f ks) ((Nat) x0) ((List (RPop)) pops) -> Type)
  enum
  (many MkPopHit : (erased (List (Nat)) e f ks) (erased (Nat) x0 s) (erased (List (Sub)) p) (erased (List (RPop)) pops)
      (erased (Mem (RPop) (MkRPop p s) pops) m) (erased (ExactAt e f ks x0 p) ex) -> (PopHit e f ks x0 pops)))

(def-adts $ (RSuf : ((List (RPop)) acc acc2) -> Type)
  enum
  (many SufZ : (erased (List (RPop)) acc) -> (RSuf acc acc))
  (many SufS : (erased (List (RPop)) acc acc2) (erased (RPop) x) (erased (RSuf acc acc2) r) -> (RSuf acc (Cons (RPop) x acc2))))

(def-fns _ $ (erased suf-trans : (erased (List (RPop)) a b c) (erased (RSuf a b) p) (subterm erased (RSuf b c) q) -> (erased (RSuf a c) r))
  (match erased q _
    ((SufZ _) p)
    ((SufS _ c1 x q1) (SufS a c1 x (suf-trans a b c1 p q1)))))

(def-fns _ $ (erased mem-suf : (erased (RPop) x) (erased (List (RPop)) a b) (erased (Mem (RPop) x a) m) (subterm erased (RSuf a b) q)
    -> (erased (Mem (RPop) x b) r))
  (match erased q _
    ((SufZ _) m)
    ((SufS _ b1 y q1) (MemThere (RPop) x y b1 (mem-suf x a b1 m q1)))))

(def-fns _ $ (erased pophit-suf : (erased (List (Nat)) e f ks) (erased (Nat) x0) (erased (List (RPop)) a b) (erased (PopHit e f ks x0 a) h)
    (erased (RSuf a b) q) -> (erased (PopHit e f ks x0 b) r))
  (let-match erased h (MkPopHit _ _ _ _ s p _ m ex))
  (MkPopHit e f ks x0 s p b (mem-suf (MkRPop p s) a b m q) ex))

(def-adts $ (RTest : ((List (Sub)) p) ((RDart) t) ((Nat) qa) ((List (RPop)) acc) ((List (Sub)) p2) ((List (RPop)) acc2) -> Type)
  enum
  (many TstH : (erased (List (Sub)) p) (erased (RDart) t) (erased (Nat) qa) (erased (List (RPop)) acc) (erased (RFaceOf t (FH)) fo)
      (erased (Length (Sub) p qa) l) -> (RTest p t qa acc p acc))
  (many TstS : (erased (List (Sub)) p) (erased (RDart) t) (erased (Nat) qa) (erased (List (RPop)) acc) (erased (RFace) i) (erased (RFaceOf t i) fo)
      (erased (RRange p i (MkRg qa qa)) rr) (erased (Lt qa 9) l) -> (RTest p t qa acc p acc))
  (many TstP : (erased (List (Sub)) p p1 p2) (erased (RDart) t) (erased (Nat) lo h1 j) (erased (List (RPop)) acc) (erased (RFace) i)
      (erased (RFaceOf t i) fo) (erased (RRange p i (MkRg lo (Succ h1))) rr) (erased (Lt (Succ h1) 9) l)
      (erased (RNarrow p i (MkRg (Succ h1) (Succ h1)) p1) n1) (erased (RNarrow p i (MkRg lo h1) p2) n2)
      -> (RTest p t (Succ h1) acc p1 (Cons (RPop) (MkRPop p2 j) acc))))

(def-fns _ $ (erased rtest-suf : (erased (List (Sub)) p p2) (erased (RDart) t) (erased (Nat) qa) (erased (List (RPop)) acc acc2)
    (erased (RTest p t qa acc p2 acc2) ts) -> (erased (RSuf acc acc2) r))
  (match erased ts _
    ((TstH _ _ _ _ _ _) (SufZ acc))
    ((TstS _ _ _ _ _ _ _ _) (SufZ acc))
    ((TstP _ _ p3 _ _ _ j _ _ _ _ _ _ _) (SufS acc acc (MkRPop p3 j) (SufZ acc)))))

(def-fns _ $ (erased rg-pop : (erased (Nat) c lo h1) (erased (InRg c (MkRg lo (Succ h1))) ic)
    -> (erased (Or (InRg c (MkRg (Succ h1) (Succ h1))) (InRg c (MkRg lo h1))) r))
  (let-match erased ic (MkInRg _ m _ _ cl l u))
  (match erased (nat-cmp m (Succ h1)) _
    ((CLt _ _ _ _ q) (OrR _ _ (MkInRg c m lo h1 cl l q)))
    ((CEq _ _ _) (OrL _ _ (MkInRg c m m m cl (lt-succ m) (lt-succ m))))
    (absurd (CGt _ _ _ _ q) (lt-le-absurd (Succ h1) m q u))))

(def-fns _ $ (erased rtest-sound : (erased (Nat) d x0 y qa) (erased (List (Nat)) e n f ks) (erased (List (Sub)) p p2) (erased (Geo d e n f ks) g)
    (erased (ExactAt e f ks x0 p) ex) (erased (RDart) t) (erased (List (RPop)) acc acc2) (erased (RTest p t qa acc p2 acc2) ts)
    (erased (RSem e f x0 t y) s) (erased (Lt y d) ly)
    -> (erased (Or (Both (Nth (Nat) ks y qa) (ExactAt e f ks x0 p2)) (PopHit e f ks x0 acc2)) r))
  (match erased ts _
    ((TstH _ _ _ _ fo l)
      (let ((erased b) (erased c) (erased bb) (erased lb) (erased pb) (erased py)) (rsem-base d x0 y e n f ks g t (FH) s fo ly))
      (let-match erased (nth-fn _ ks b c qa pb (rknown-sound d x0 b qa e n f ks p g ex (FH) (KH p qa l) bb lb)) (Refl _ _))
      (OrL _ _ (MkBoth _ _ py ex)))
    ((TstS _ _ _ _ i fo rr l)
      (let ((erased b) (erased c) (erased bb) (erased lb) (erased pb) (erased py)) (rsem-base d x0 y e n f ks g t i s fo ly))
      (let-match erased (in-single c qa (rrange-sound x0 b c e f ks p ex i (MkRg qa qa) rr bb pb) l) (Refl _ _))
      (OrL _ _ (MkBoth _ _ py ex)))
    ((TstP _ _ p3 _ lo h1 j _ i fo rr l n1 n2)
      (let ((erased b) (erased c) (erased bb) (erased lb) (erased pb) (erased py)) (rsem-base d x0 y e n f ks g t i s fo ly))
      (match erased (rg-pop c lo h1 (rrange-sound x0 b c e f ks p ex i (MkRg lo (Succ h1)) rr bb pb)) _
        ((OrL _ _ ic)
          (let-match erased (in-single c (Succ h1) ic l) (Refl _ _))
          (OrL _ _ (MkBoth _ _ py (rnarrow-sound x0 b c e f ks p p2 ex i (MkRg (Succ h1) (Succ h1)) n1 bb pb ic))))
        ((OrR _ _ ic)
          (OrR _ _ (MkPopHit e f ks x0 j p3 acc2 (MemHere (RPop) (MkRPop p3 j) acc) (rnarrow-sound x0 b c e f ks p p3 ex i (MkRg lo h1) n2 bb pb ic))))))))

(def-adts $ (RWalk : ((List (Sub)) p) ((RDart) t) ((Qn) q) ((List (RPop)) acc) ((List (Sub)) p2) ((List (RPop)) acc2) -> Type)
  enum
  (many W0 : (erased (List (Sub)) p) (erased (RDart) t) (erased (List (RPop)) acc) -> (RWalk p t (Qask0) acc p acc))
  (many W1 : (erased (List (Sub)) p p1) (erased (RDart) t) (erased (Nat) qa) (erased (List (RPop)) acc acc1) (erased (RTest p t qa acc p1 acc1) ts)
      -> (RWalk p t (Qask1 qa) acc p1 acc1))
  (many WL : (erased (List (Sub)) p p1 p2) (erased (RDart) t t1) (erased (Nat) qa) (erased (Qn) q) (erased (List (RPop)) acc acc1 acc2)
      (erased (RTest p t qa acc p1 acc1) ts) (erased (RQl p1 t t1) st) (erased (RWalk p1 t1 q acc1 p2 acc2) w) -> (RWalk p t (QaskL qa q) acc p2 acc2))
  (many WR : (erased (List (Sub)) p p1 p2) (erased (RDart) t t1) (erased (Nat) qa) (erased (Qn) q) (erased (List (RPop)) acc acc1 acc2)
      (erased (RTest p t qa acc p1 acc1) ts) (erased (RQr p1 t t1) st) (erased (RWalk p1 t1 q acc1 p2 acc2) w) -> (RWalk p t (QaskR qa q) acc p2 acc2))
  (many WLR : (erased (List (Sub)) p p1 p2 p3) (erased (RDart) t tl tr) (erased (Nat) qa) (erased (Qn) ql qr) (erased (List (RPop)) acc acc1 acc2 acc3)
      (erased (RTest p t qa acc p1 acc1) ts) (erased (RQl p1 t tl) sl) (erased (RWalk p1 tl ql acc1 p2 acc2) wl) (erased (RQr p2 t tr) sr)
      (erased (RWalk p2 tr qr acc2 p3 acc3) wr) -> (RWalk p t (QaskLR qa ql qr) acc p3 acc3))
  (many WLL : (erased (List (Sub)) p p1 p2) (erased (RDart) t tl t2) (erased (Nat) qa) (erased (Qn) q) (erased (List (RPop)) acc acc1 acc2)
      (erased (RQl p t tl) s1) (erased (RTest p tl qa acc p1 acc1) ts) (erased (RQl p1 tl t2) s2) (erased (RWalk p1 t2 q acc1 p2 acc2) w)
      -> (RWalk p t (QaskLL qa q) acc p2 acc2))
  (many WRR : (erased (List (Sub)) p p1 p2) (erased (RDart) t tr t2) (erased (Nat) qa) (erased (Qn) q) (erased (List (RPop)) acc acc1 acc2)
      (erased (RQr p t tr) s1) (erased (RTest p tr qa acc p1 acc1) ts) (erased (RQr p1 tr t2) s2) (erased (RWalk p1 t2 q acc1 p2 acc2) w)
      -> (RWalk p t (QaskRR qa q) acc p2 acc2)))

(def-fns _ $ (erased rwalk-suf : (erased (List (Sub)) p p2) (erased (RDart) t) (erased (Qn) q) (erased (List (RPop)) acc acc2)
    (subterm erased (RWalk p t q acc p2 acc2) w) -> (erased (RSuf acc acc2) r))
  (match erased w _
    ((W0 _ _ _) (SufZ acc))
    ((W1 _ _ _ qa _ _ ts) (rtest-suf p p2 t qa acc acc2 ts))
    ((WL _ p1 _ _ t1 qa q1 _ acc1 _ ts _ w1)
      (suf-trans acc acc1 acc2 (rtest-suf p p1 t qa acc acc1 ts) (rwalk-suf p1 p2 t1 q1 acc1 acc2 w1)))
    ((WR _ p1 _ _ t1 qa q1 _ acc1 _ ts _ w1)
      (suf-trans acc acc1 acc2 (rtest-suf p p1 t qa acc acc1 ts) (rwalk-suf p1 p2 t1 q1 acc1 acc2 w1)))
    ((WLR _ p1 p3 _ _ tl tr qa ql qr _ acc1 acc3 _ ts _ wl _ wr)
      (suf-trans acc acc1 acc2 (rtest-suf p p1 t qa acc acc1 ts)
        (suf-trans acc1 acc3 acc2 (rwalk-suf p1 p3 tl ql acc1 acc3 wl) (rwalk-suf p3 p2 tr qr acc3 acc2 wr))))
    ((WLL _ p1 _ _ tl t2 qa q1 _ acc1 _ _ ts _ w1)
      (suf-trans acc acc1 acc2 (rtest-suf p p1 tl qa acc acc1 ts) (rwalk-suf p1 p2 t2 q1 acc1 acc2 w1)))
    ((WRR _ p1 _ _ tr t2 qa q1 _ acc1 _ _ ts _ w1)
      (suf-trans acc acc1 acc2 (rtest-suf p p1 tr qa acc acc1 ts) (rwalk-suf p1 p2 t2 q1 acc1 acc2 w1)))))

(def-fns _ $ (erased edge-node-arity : (erased (Nat) d x c c2 a) (erased (List (Nat)) e n f ks) (erased (Geo d e n f ks) g) (erased (Lt x d) lx)
    (erased (Nth (Nat) n x c) pc) (erased (Nth (Nat) e c c2) pc2) (erased (Nth (Nat) ks x a) pa) -> (erased (Nth (Nat) ks c2 a) r))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ ol _))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased qe) (erased qn) (erased qf)) (hyper-core d e n f h))
  (let ((erased lc2)) (img-lt d c c2 e nf qe (img-lt d x c n ni qn lx pc) pc2))
  (let ((erased a2) (erased pa2) (erased _)) (arity-at d c2 f ks ol lc2))
  (let-match erased (arity-same d c2 x 1 a2 a e n f ks g lc2 pa2 (one-step f c2 x (fen d x c c2 e n f h lx pc pc2)) pa) (Refl _ _))
  pa2)

(def-fns _ $ (erased rwalk-sound : (erased (Nat) d x0 y) (erased (List (Nat)) e n f ks) (erased (List (Sub)) p p2) (erased (Geo d e n f ks) g)
    (erased (ExactAt e f ks x0 p) ex) (erased (RDart) t) (erased (Qn) q) (erased (List (RPop)) acc acc2) (subterm erased (RWalk p t q acc p2 acc2) w)
    (erased (RSem e f x0 t y) s) (erased (Lt y d) ly)
    -> (erased (Or (Both (FitQ e n ks y q) (ExactAt e f ks x0 p2)) (PopHit e f ks x0 acc2)) r))
  (match erased w _
    ((W0 _ _ _) (OrL _ _ (MkBoth _ _ (FQ0 e n ks y) ex)))
    ((W1 _ _ _ qa _ _ ts)
      (match erased (rtest-sound d x0 y qa e n f ks p p2 g ex t acc acc2 ts s ly) _
        ((OrL _ _ b) (let-match erased b (MkBoth _ _ pa ex1)) (OrL _ _ (MkBoth _ _ (FQ1 e n ks y qa pa) ex1)))
        ((OrR _ _ ph) (OrR _ _ ph))))
    ((WL _ p1 _ _ t1 qa q1 _ acc1 _ ts st w1)
      (match erased (rtest-sound d x0 y qa e n f ks p p1 g ex t acc acc1 ts s ly) _
        ((OrR _ _ ph) (OrR _ _ (pophit-suf e f ks x0 acc1 acc2 ph (rwalk-suf p1 p2 t1 q1 acc1 acc2 w1))))
        ((OrL _ _ b)
          (let-match erased b (MkBoth _ _ pa ex1))
          (let ((erased z) (erased sz) (erased s1) (erased lz)) (rql-sound d x0 y e n f ks p1 g ex1 t t1 st s ly))
          (match erased (rwalk-sound d x0 z e n f ks p1 p2 g ex1 t1 q1 acc1 acc2 w1 s1 lz) _
            ((OrL _ _ b2) (let-match erased b2 (MkBoth _ _ fq ex2)) (OrL _ _ (MkBoth _ _ (FQL e n ks y qa z q1 pa sz fq) ex2)))
            ((OrR _ _ ph) (OrR _ _ ph))))))
    ((WR _ p1 _ _ t1 qa q1 _ acc1 _ ts st w1)
      (match erased (rtest-sound d x0 y qa e n f ks p p1 g ex t acc acc1 ts s ly) _
        ((OrR _ _ ph) (OrR _ _ (pophit-suf e f ks x0 acc1 acc2 ph (rwalk-suf p1 p2 t1 q1 acc1 acc2 w1))))
        ((OrL _ _ b)
          (let-match erased b (MkBoth _ _ pa ex1))
          (let ((erased z) (erased sz) (erased s1) (erased lz)) (rqr-sound d x0 y e n f ks p1 g ex1 t t1 st s ly))
          (match erased (rwalk-sound d x0 z e n f ks p1 p2 g ex1 t1 q1 acc1 acc2 w1 s1 lz) _
            ((OrL _ _ b2) (let-match erased b2 (MkBoth _ _ fq ex2)) (OrL _ _ (MkBoth _ _ (FQR e n ks y qa z q1 pa sz fq) ex2)))
            ((OrR _ _ ph) (OrR _ _ ph))))))
    ((WLR _ p1 p3 _ _ tl tr qa ql qr _ acc1 acc3 _ ts sl wl sr wr)
      (match erased (rtest-sound d x0 y qa e n f ks p p1 g ex t acc acc1 ts s ly) _
        ((OrR _ _ ph)
          (OrR _ _ (pophit-suf e f ks x0 acc1 acc2 ph
            (suf-trans acc1 acc3 acc2 (rwalk-suf p1 p3 tl ql acc1 acc3 wl) (rwalk-suf p3 p2 tr qr acc3 acc2 wr)))))
        ((OrL _ _ b)
          (let-match erased b (MkBoth _ _ pa ex1))
          (let ((erased zl) (erased szl) (erased s1) (erased lzl)) (rql-sound d x0 y e n f ks p1 g ex1 t tl sl s ly))
          (match erased (rwalk-sound d x0 zl e n f ks p1 p3 g ex1 tl ql acc1 acc3 wl s1 lzl) _
            ((OrR _ _ ph) (OrR _ _ (pophit-suf e f ks x0 acc3 acc2 ph (rwalk-suf p3 p2 tr qr acc3 acc2 wr))))
            ((OrL _ _ b2)
              (let-match erased b2 (MkBoth _ _ fql ex2))
              (let ((erased zr) (erased szr) (erased s2) (erased lzr)) (rqr-sound d x0 y e n f ks p3 g ex2 t tr sr s ly))
              (match erased (rwalk-sound d x0 zr e n f ks p3 p2 g ex2 tr qr acc3 acc2 wr s2 lzr) _
                ((OrL _ _ b3) (let-match erased b3 (MkBoth _ _ fqr ex3)) (OrL _ _ (MkBoth _ _ (FQLR e n ks y qa zl zr ql qr pa szl fql szr fqr) ex3)))
                ((OrR _ _ ph) (OrR _ _ ph))))))))
    ((WLL _ p1 _ _ tl t2 qa q1 _ acc1 _ s1 ts s2 w1)
      (let ((erased xl) (erased sxl) (erased sl) (erased lxl)) (rql-sound d x0 y e n f ks p g ex t tl s1 s ly))
      (match erased (rtest-sound d x0 xl qa e n f ks p p1 g ex tl acc acc1 ts sl lxl) _
        ((OrR _ _ ph) (OrR _ _ (pophit-suf e f ks x0 acc1 acc2 ph (rwalk-suf p1 p2 t2 q1 acc1 acc2 w1))))
        ((OrL _ _ b)
          (let-match erased b (MkBoth _ _ pa ex1))
          (let ((erased z) (erased sz) (erased s3) (erased lz)) (rql-sound d x0 xl e n f ks p1 g ex1 tl t2 s2 sl lxl))
          (let-match erased g (MkGeo _ _ _ _ _ h _ _ _ _))
          (let ((erased _) (erased c) (erased _) (erased _) (erased _) (erased pc) (erased lc) (erased _) (erased _)) (hyper-step d xl e n f h lxl))
          (let ((erased c2) (erased _) (erased _) (erased pc2) (erased _) (erased _) (erased _) (erased _) (erased _)) (hyper-step d c e n f h lc))
          (match erased (rwalk-sound d x0 z e n f ks p1 p2 g ex1 t2 q1 acc1 acc2 w1 s3 lz) _
            ((OrL _ _ b2)
              (let-match erased b2 (MkBoth _ _ fq ex2))
              (OrL _ _ (MkBoth _ _ (FQLL e n ks y qa xl c c2 z q1 sxl pc pc2 (edge-node-arity d xl c c2 qa e n f ks g lxl pc pc2 pa) sz fq) ex2)))
            ((OrR _ _ ph) (OrR _ _ ph))))))
    ((WRR _ p1 _ _ tr t2 qa q1 _ acc1 _ s1 ts s2 w1)
      (let ((erased xr) (erased sxr) (erased sr) (erased lxr)) (rqr-sound d x0 y e n f ks p g ex t tr s1 s ly))
      (match erased (rtest-sound d x0 xr qa e n f ks p p1 g ex tr acc acc1 ts sr lxr) _
        ((OrR _ _ ph) (OrR _ _ (pophit-suf e f ks x0 acc1 acc2 ph (rwalk-suf p1 p2 t2 q1 acc1 acc2 w1))))
        ((OrL _ _ b)
          (let-match erased b (MkBoth _ _ pa ex1))
          (let ((erased z) (erased sz) (erased s3) (erased lz)) (rqr-sound d x0 xr e n f ks p1 g ex1 tr t2 s2 sr lxr))
          (match erased (rwalk-sound d x0 z e n f ks p1 p2 g ex1 t2 q1 acc1 acc2 w1 s3 lz) _
            ((OrL _ _ b2) (let-match erased b2 (MkBoth _ _ fq ex2)) (OrL _ _ (MkBoth _ _ (FQRR e n ks y qa xr z q1 sxr pa sz fq) ex2)))
            ((OrR _ _ ph) (OrR _ _ ph))))))))

(def-adts $ (RWalkR : ((List (Sub)) p) ((RDart) x) ((Qn) q) ((List (RPop)) acc) ((List (Sub)) p2) ((List (RPop)) acc2) -> Type)
  enum
  (many WR0 : (erased (List (Sub)) p) (erased (RDart) x) (erased (List (RPop)) acc) -> (RWalkR p x (Qask0) acc p acc))
  (many WRS : (erased (List (Sub)) p p2) (erased (RDart) x z) (erased (Qn) q) (erased (List (RPop)) acc acc2) (erased (RQr p x z) st)
      (erased (RWalk p z q acc p2 acc2) w) -> (RWalkR p x q acc p2 acc2)))

(def-adts $ (FitR : ((List (Nat)) e n ks) ((Nat) x) ((Qn) q) -> Type)
  enum
  (many MkFitR : (erased (List (Nat)) e n ks) (erased (Nat) x z) (erased (Qn) q) (erased (QStepR e n x z) s) (erased (FitQ e n ks z q) r)
      -> (FitR e n ks x q)))

(def-fns _ $ (erased rwalkr-suf : (erased (List (Sub)) p p2) (erased (RDart) x) (erased (Qn) q) (erased (List (RPop)) acc acc2)
    (erased (RWalkR p x q acc p2 acc2) w) -> (erased (RSuf acc acc2) r))
  (match erased w _
    ((WR0 _ _ _) (SufZ acc))
    ((WRS _ _ _ z _ _ _ _ w1) (rwalk-suf p p2 z q acc acc2 w1))))

(def-fns _ $ (erased rwalkr-sound : (erased (Nat) d x0 y) (erased (List (Nat)) e n f ks) (erased (List (Sub)) p p2) (erased (Geo d e n f ks) g)
    (erased (ExactAt e f ks x0 p) ex) (erased (RDart) x) (erased (Qn) q) (erased (List (RPop)) acc acc2) (erased (RWalkR p x q acc p2 acc2) w)
    (erased (RSem e f x0 x y) s) (erased (Lt y d) ly)
    -> (erased (Or (Both (FitR e n ks y q) (ExactAt e f ks x0 p2)) (PopHit e f ks x0 acc2)) r))
  (match erased w _
    ((WR0 _ _ _)
      (let-match erased g (MkGeo _ _ _ _ _ h _ _ _ _))
      (let ((erased a) (erased _) (erased _) (erased pa) (erased la) (erased _) (erased _) (erased _) (erased _)) (hyper-step d y e n f h ly))
      (let ((erased _) (erased z) (erased _) (erased _) (erased _) (erased pz) (erased _) (erased _) (erased _)) (hyper-step d a e n f h la))
      (OrL _ _ (MkBoth _ _ (MkFitR e n ks y z (Qask0) (MkQStepR e n y a z pa pz) (FQ0 e n ks z)) ex)))
    ((WRS _ _ _ z0 _ _ _ st w1)
      (let ((erased z) (erased sz) (erased s1) (erased lz)) (rqr-sound d x0 y e n f ks p g ex x z0 st s ly))
      (match erased (rwalk-sound d x0 z e n f ks p p2 g ex z0 q acc acc2 w1 s1 lz) _
        ((OrL _ _ b) (let-match erased b (MkBoth _ _ fq ex2)) (OrL _ _ (MkBoth _ _ (MkFitR e n ks y z q sz fq) ex2)))
        ((OrR _ _ ph) (OrR _ _ ph))))))

(def-adts $ (RLeafs : ((List (Sub)) p) ((List (RPop)) acc) ((RDart) x1 x2 x3) ((Qzt) t) ((List (RPop)) acc2) -> Type)
  enum
  (many MkRLeafs : (erased (List (Sub)) p p4 p5 p6) (erased (List (RPop)) acc c4 c5 acc2) (erased (RDart) x1 x2 x3) (erased (Qzt) t)
      (erased (Qn) q1 q2 q3) (erased (QLeaf t q1 q2 q3) lf) (erased (RWalkR p x1 q1 acc p4 c4) w1) (erased (RWalkR p4 x2 q2 c4 p5 c5) w2)
      (erased (RWalkR p5 x3 q3 c5 p6 acc2) w3) -> (RLeafs p acc x1 x2 x3 t acc2)))

(def-adts $ (RHit : ((Qzt) qt) ((List (Sub)) p) ((List (RPop)) pops) -> Type)
  enum
  (many MkRHit : (erased (Qzt) qt t1 t2 t3) (erased (List (Sub)) p p1 p2 p3) (erased (RDart) x1 x2 x3) (erased (Nat) a1 a2 a3)
      (erased (List (RPop)) c1 c2 c3 pops) (erased (RNs p x1 x2) n2) (erased (RNs p x2 x3) n3)
      (erased (RTest p x1 a1 (Nil (RPop)) p1 c1) s1) (erased (RTest p1 x2 a2 c1 p2 c2) s2) (erased (RTest p2 x3 a3 c2 p3 c3) s3)
      (erased (QGet a1 qt t1) g1) (erased (QGet a2 t1 t2) g2) (erased (QGet a3 t2 t3) g3) (erased (RLeafs p3 c3 x1 x2 x3 t3 pops) lw)
      -> (RHit qt p pops)))

(def-fns _ $ (erased rhit-sound : (erased (Nat) d x0) (erased (List (Nat)) e n f ks) (erased (Qzt) qt) (erased (List (Sub)) p) (erased (List (RPop)) pops)
    (erased (Geo d e n f ks) g) (erased (Lt x0 d) lx) (erased (ExactAt e f ks x0 p) ex) (erased (RHit qt p pops) hh)
    -> (erased (Or (HasFit d e n ks qt) (PopHit e f ks x0 pops)) r))
  (let-match erased g (MkGeo _ _ _ _ _ h _ _ _ _))
  (let-match erased hh (MkRHit _ t1 t2 t3 _ p1 p2 p3 x1 x2 x3 a1 a2 a3 c1 c2 c3 _ n2 n3 s1 s2 s3 g1 g2 g3 lw))
  (let-match erased lw (MkRLeafs _ p4 p5 p6 _ c4 c5 _ _ _ _ _ q1 q2 q3 lf w1 w2 w3))
  (let ((erased y1) (erased sy1) (erased ly1)) (rsem-ex d x0 e n f h lx x1))
  (let ((erased y2) (erased py2) (erased sy2) (erased ly2)) (rns-sound d x0 y1 e n f ks p g ex x1 x2 n2 sy1 ly1))
  (let ((erased y3) (erased py3) (erased sy3) (erased ly3)) (rns-sound d x0 y2 e n f ks p g ex x2 x3 n3 sy2 ly2))
  (let ((erased u1)) (suf-trans (Nil (RPop)) c1 c2 (rtest-suf p p1 x1 a1 (Nil (RPop)) c1 s1) (rtest-suf p1 p2 x2 a2 c1 c2 s2)))
  (let ((erased u2)) (suf-trans (Nil (RPop)) c2 c3 u1 (rtest-suf p2 p3 x3 a3 c2 c3 s3)))
  (let ((erased v1)) (suf-trans c3 c4 c5 (rwalkr-suf p3 p4 x1 q1 c3 c4 w1) (rwalkr-suf p4 p5 x2 q2 c4 c5 w2)))
  (let ((erased v2)) (suf-trans c3 c5 pops v1 (rwalkr-suf p5 p6 x3 q3 c5 pops w3)))
  (match erased (rtest-sound d x0 y1 a1 e n f ks p p1 g ex x1 (Nil (RPop)) c1 s1 sy1 ly1) _
    ((OrR _ _ ph)
      (OrR _ _ (pophit-suf e f ks x0 c1 pops ph (suf-trans c1 c3 pops (suf-trans c1 c2 c3 (rtest-suf p1 p2 x2 a2 c1 c2 s2) (rtest-suf p2 p3 x3 a3 c2 c3 s3)) v2))))
    ((OrL _ _ b1)
      (let-match erased b1 (MkBoth _ _ k1 e1))
      (match erased (rtest-sound d x0 y2 a2 e n f ks p1 p2 g e1 x2 c1 c2 s2 sy2 ly2) _
        ((OrR _ _ ph) (OrR _ _ (pophit-suf e f ks x0 c2 pops ph (suf-trans c2 c3 pops (rtest-suf p2 p3 x3 a3 c2 c3 s3) v2))))
        ((OrL _ _ b2)
          (let-match erased b2 (MkBoth _ _ k2 e2))
          (match erased (rtest-sound d x0 y3 a3 e n f ks p2 p3 g e2 x3 c2 c3 s3 sy3 ly3) _
            ((OrR _ _ ph) (OrR _ _ (pophit-suf e f ks x0 c3 pops ph v2)))
            ((OrL _ _ b3)
              (let-match erased b3 (MkBoth _ _ k3 e3))
              (match erased (rwalkr-sound d x0 y1 e n f ks p3 p4 g e3 x1 q1 c3 c4 w1 sy1 ly1) _
                ((OrR _ _ ph) (OrR _ _ (pophit-suf e f ks x0 c4 pops ph (suf-trans c4 c5 pops (rwalkr-suf p4 p5 x2 q2 c4 c5 w2) (rwalkr-suf p5 p6 x3 q3 c5 pops w3)))))
                ((OrL _ _ b4)
                  (let-match erased b4 (MkBoth _ _ r1 e4))
                  (match erased (rwalkr-sound d x0 y2 e n f ks p4 p5 g e4 x2 q2 c4 c5 w2 sy2 ly2) _
                    ((OrR _ _ ph) (OrR _ _ (pophit-suf e f ks x0 c5 pops ph (rwalkr-suf p5 p6 x3 q3 c5 pops w3))))
                    ((OrL _ _ b5)
                      (let-match erased b5 (MkBoth _ _ r2 e5))
                      (match erased (rwalkr-sound d x0 y3 e n f ks p5 p6 g e5 x3 q3 c5 pops w3 sy3 ly3) _
                        ((OrR _ _ ph) (OrR _ _ ph))
                        ((OrL _ _ b6)
                          (let-match erased b6 (MkBoth _ _ r3 _))
                          (let-match erased r1 (MkFitR _ _ _ _ z1 _ st1 f1))
                          (let-match erased r2 (MkFitR _ _ _ _ z2 _ st2 f2))
                          (let-match erased r3 (MkFitR _ _ _ _ z3 _ st3 f3))
                          (OrL _ _ (MkHasFit d y1 e n ks qt ly1 (MkQztFit e n ks qt t1 t2 t3 y1 y2 y3 a1 a2 a3 z1 z2 z3 q1 q2 q3 py2 py3 k1 k2 k3
                            g1 g2 g3 lf st1 f1 st2 f2 st3 f3))))))))))))))))

(def-adts
  ((RedD : ((Qzt) qt) ((List (Sub)) p) -> Type)
    enum
    (many MkRedD : (erased (Qzt) qt) (erased (List (Sub)) p) (erased (List (RPop)) pops) (erased (RHit qt p pops) h) (erased (RedL qt pops) r)
        -> (RedD qt p)))
  ((RedL : ((Qzt) qt) ((List (RPop)) pops) -> Type)
    enum
    (many RLNil : (erased (Qzt) qt) -> (RedL qt (Nil (RPop))))
    (many RLCons : (erased (Qzt) qt) (erased (List (Sub)) p) (erased (Nat) s) (erased (List (RPop)) rest) (erased (RedD qt p) dd)
        (erased (RedL qt rest) r) -> (RedL qt (Cons (RPop) (MkRPop p s) rest)))))

(def-fns _
  ((erased red-sound : (erased (Nat) d x0) (erased (List (Nat)) e n f ks) (erased (Qzt) qt) (erased (List (Sub)) p) (subterm erased (RedD qt p) r)
      (erased (Geo d e n f ks) g) (erased (Lt x0 d) lx) (erased (ExactAt e f ks x0 p) ex) -> (erased (HasFit d e n ks qt) q))
    (let-match erased r (MkRedD _ _ pops hh rl))
    (match erased (rhit-sound d x0 e n f ks qt p pops g lx ex hh) _
      ((OrL _ _ hf) hf)
      ((OrR _ _ ph)
        (let-match erased ph (MkPopHit _ _ _ _ s pp _ m ex2))
        (redl-sound d x0 e n f ks qt pops rl g lx pp s m ex2))))
  ((erased redl-sound : (erased (Nat) d x0) (erased (List (Nat)) e n f ks) (erased (Qzt) qt) (erased (List (RPop)) pops) (subterm erased (RedL qt pops) r)
      (erased (Geo d e n f ks) g) (erased (Lt x0 d) lx) (erased (List (Sub)) pp) (erased (Nat) s) (erased (Mem (RPop) (MkRPop pp s) pops) m)
      (erased (ExactAt e f ks x0 pp) ex) -> (erased (HasFit d e n ks qt) q))
    (let-match erased r (RLCons _ p1 s1 rest d1 r1) (absurd (RLNil _) m))
    (match erased m _
      ((MemHere _ _ _) (red-sound d x0 e n f ks qt p1 d1 g lx ex))
      ((MemThere _ _ _ _ m1) (redl-sound d x0 e n f ks qt rest r1 g lx pp s m1 ex)))))
