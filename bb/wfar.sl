(def-fns _ $ (erased add-ar : (erased (Nat) a b c x y) (subterm erased (Add a b x) p) (erased (Add x c y) q) ->
    (erased (Nat) z) (erased (Add b c z) r) (erased (Add a z y) s))
  (let-match erased p (AddSucc a1 _ x1 p1) ((AddZero _) (values y q (AddZero y))))
  (let-match erased q (AddSucc _ _ y1 q1))
  (let ((erased z) (erased r) (erased s)) (add-ar a1 b c x1 y1 p1 q1))
  (values z r (AddSucc a1 z y1 s)))

(def-fns _ $ (erased add-al : (erased (Nat) a b c z y) (erased (Add b c z) p) (subterm erased (Add a z y) q) ->
    (erased (Nat) x) (erased (Add a b x) r) (erased (Add x c y) s))
  (let-match erased q (AddSucc a1 _ y1 q1) ((AddZero _) (values b (AddZero b) p)))
  (let ((erased x1) (erased r1) (erased s1)) (add-al a1 b c z y1 p q1))
  (values (Succ x1) (AddSucc a1 b x1 r1) (AddSucc x1 c y1 s1)))

(def-fns _ $ (erased add-sw : (erased (Nat) a b c x y) (erased (Add a b x) p) (erased (Add x c y) q) ->
    (erased (Nat) w) (erased (Add a c w) r) (erased (Add w b y) s))
  (let ((erased z) (erased r1) (erased s1)) (add-ar a b c x y p q))
  (add-al a c b z y (add-comm b c z r1) s1))

(def-fns _ $ (erased add-ic : (erased (Nat) a b c d x y s) (erased (Add a b x) p) (erased (Add c d y) q) (erased (Add x y s) t) ->
    (erased (Nat) u v) (erased (Add a c u) r1) (erased (Add b d v) r2) (erased (Add u v s) r3))
  (let ((erased z1) (erased b1) (erased a1)) (add-ar a b y x s p t))
  (let ((erased z2) (erased b2) (erased c2)) (add-al b c d y z1 q b1))
  (let ((erased v) (erased bdv) (erased cv)) (add-ar c b d z2 z1 (add-comm b c z2 b2) c2))
  (let ((erased u) (erased ac) (erased uv)) (add-al a c v z1 s cv a1))
  (values u v ac bdv uv))

(def-fns _ $ (erased step-id : (erased (Nat) ha hb hk hp hx u ha2 hb2 w v t hc2 hp2 hx2 k)
    (erased (Add ha hb hp) ab) (erased (Add hp hk hx) pc) (erased (Add ha u ha2) au) (erased (Add hb2 w hb) bw) (erased (Add hk v t) cv)
    (erased (Add t w hc2) tw) (erased (Add ha2 hb2 hp2) ab2) (erased (Add hp2 hc2 hx2) pc2) (erased (Add u v k) uv) -> (erased (Add hx k hx2) r))
  (let ((erased w1) (erased e1) (erased e2)) (add-sw ha u hb2 ha2 hp2 au ab2))
  (let ((erased w2) (erased e3) (erased e4)) (add-sw hk v w t hc2 cv tw))
  (let ((erased u1) (erased v1) (erased e5) (erased e6) (erased e7)) (add-ic w1 u w2 v hp2 hc2 hx2 e2 e4 pc2))
  (let-match erased (add-fn u v v1 k e6 uv) (Refl _ _))
  (let ((erased u2) (erased v2) (erased e8) (erased e9) (erased e10)) (add-ic ha hb2 hk w w1 w2 u1 e1 e3 e5))
  (let-match erased (add-fn hb2 w v2 hb e9 bw) (Refl _ _))
  (let ((erased w3) (erased e11) (erased e12)) (add-sw ha hb hk hp hx ab pc))
  (let-match erased (add-fn ha hk u2 w3 e8 e11) (Refl _ _))
  (let-match erased (add-fn u2 hb u1 hx e10 e12) (Refl _ _))
  e7)

(def-adts $ (Ord : -> Type)
  enum
  (many OEq : -> (Ord))
  (many OGe : -> (Ord))
  (many OLe : -> (Ord)))

(def-adts
  ((Rel : ((Ord) g) ((Nat) x) ((Nat) y) -> Type)
    enum
    (many REq : (erased (Nat) x) -> (Rel (OEq) x x))
    (many RGe : (erased (Nat) x y e) (erased (Add y e x) p) -> (Rel (OGe) x y))
    (many RLe : (erased (Nat) x y e) (erased (Add x e y) p) -> (Rel (OLe) x y))))

(def-fns _ $ (erased rel-add : (erased (Ord) g) (erased (Nat) x y k x2 y2) (erased (Rel g x y) rl) (erased (Add x k x2) px) (erased (Add y k y2) py)
    -> (erased (Rel g x2 y2) r))
  (match erased rl _
    ((REq _) (let-match erased (add-fn x k x2 y2 px py) (Refl _ _)) (REq x2))
    ((RGe _ _ e p)
      (let ((erased w) (erased a) (erased b)) (add-sw y e k x x2 p px))
      (let-match erased (add-fn y k w y2 a py) (Refl _ _))
      (RGe x2 y2 e b))
    ((RLe _ _ e p)
      (let ((erased w) (erased a) (erased b)) (add-sw x e k y y2 p py))
      (let-match erased (add-fn x k w x2 a px) (Refl _ _))
      (RLe x2 y2 e b))))

(def-adts $ (WR : -> Type)
  enum
  (many MkWR : (many (Nat) u0 p0 n0 u1 p1 n1) -> (WR)))

(def-adts
  ((WEdge : ((List (WR)) w) ((Nat) u) ((Bool) c) ((Nat) v) ((Nat) p) ((Nat) n) -> Type)
    enum
    (many WE0 : (erased (List (WR)) w) (erased (Nat) u u0 p0 n0 u1 p1 n1) (erased (Nth (WR) w u (MkWR u0 p0 n0 u1 p1 n1)) nr)
       -> (WEdge w u (BFalse) u0 p0 n0))
    (many WE1 : (erased (List (WR)) w) (erased (Nat) u u0 p0 n0 u1 p1 n1) (erased (Nth (WR) w u (MkWR u0 p0 n0 u1 p1 n1)) nr)
       -> (WEdge w u (BTrue) u1 p1 n1))))

(def-adts
  ((WRun : ((List (WR)) w) ((List (Bool)) l) ((Nat) u) ((Nat) Pa) ((Nat) Na) -> Type)
    enum
    (many WRNil : (erased (List (WR)) w) -> (WRun w (Nil (Bool)) (Zero) (Zero) (Zero)))
    (many WRCons : (erased (List (WR)) w) (erased (List (Bool)) l) (erased (Nat) u Pa Na v p n Pb Nb) (erased (Bool) c)
       (erased (WRun w l u Pa Na) r) (erased (WEdge w u c v p n) e) (erased (Add Pa p Pb) ap) (erased (Add Na n Nb) an)
       -> (WRun w (Cons (Bool) c l) v Pb Nb))))

(def-adts $ (AE : -> Type)
  enum
  (many MkAE : (many (Nat) l r) (many (Bool) m) (many (Nat) s dp dn) (many (Ord) g) -> (AE)))

(def-adts
  ((Gam : ((List (WR)) wl) ((List (WR)) wr) ((AE) a) ((Conf) c) -> Type)
    enum
    (many MkGam : (erased (List (WR)) wl wr) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn) (erased (Ord) g) (erased (List (Bool)) lt rt)
       (erased (Nat) Pl Nl Pr Nr Pa Na Xa Ya) (erased (WRun wl lt l Pl Nl) rl) (erased (WRun wr rt r Pr Nr) rr)
       (erased (Add Pl Pr Pa) ap) (erased (Add Nl Nr Na) an) (erased (Add Pa dn Xa) ax) (erased (Add Na dp Ya) ay) (erased (Rel g Xa Ya) rel)
       -> (Gam wl wr (MkAE l r m s dp dn g) (MkConf s lt m rt)))))

(def-adts
  ((SgW : ((Bool) sg) ((Nat) p) ((Nat) n) -> Type)
    enum
    (many SgN : (erased (Nat) p n f) (erased (Add p f n) a) -> (SgW (BFalse) p n))
    (many SgP : (erased (Nat) p n f) (erased (Add n f p) a) -> (SgW (BTrue) p n))))

(def-adts
  ((ECk : ((Bool) sg) ((List (Nat)) ns) ((Nat) u) ((Nat) v) ((Nat) p) ((Nat) n) -> Type)
    enum
    (many ECOut : (erased (Bool) sg) (erased (List (Nat)) ns) (erased (Nat) u v p n) (erased (NotIn v ns) ni) -> (ECk sg ns u v p n))
    (many ECIn : (erased (Bool) sg) (erased (List (Nat)) ns) (erased (Nat) u v p n) (erased (SgW sg p n) sw) (erased (Mem (Nat) u ns) mu)
       -> (ECk sg ns u v p n))))

(def-adts
  ((SC : ((Bool) sg) ((List (Nat)) ns) ((Nat) u) ((List (WR)) ws) -> Type)
    enum
    (many SCNil : (erased (Bool) sg) (erased (List (Nat)) ns) (erased (Nat) u) -> (SC sg ns u (Nil (WR))))
    (many SCCons : (erased (Bool) sg) (erased (List (Nat)) ns) (erased (Nat) u u0 p0 n0 u1 p1 n1) (erased (List (WR)) ws)
       (erased (ECk sg ns u u0 p0 n0) e0) (erased (ECk sg ns u u1 p1 n1) e1) (erased (SC sg ns (Succ u) ws) rest)
       -> (SC sg ns u (Cons (WR) (MkWR u0 p0 n0 u1 p1 n1) ws)))))

(def-fns _ $ (erased sc-get : (erased (Bool) sg) (erased (List (Nat)) ns) (erased (Nat) u0 j u v p n) (subterm erased (List (WR)) ws) (erased (Bool) c)
    (erased (SC sg ns u0 ws) sc) (erased (WEdge ws j c v p n) we) (erased (Add j u0 u) ad) -> (erased (ECk sg ns u v p n) ek))
  (match erased we _
    ((WE0 _ _ v0 p0 n0 v1 p1 n1 nr)
      (let-match erased nr (NthThere _ _ rest j1 _ nr1)
        ((NthHere _ _ _) (let-match erased ad (AddZero _)) (let-match erased sc (SCCons _ _ _ _ _ _ _ _ _ _ e0 _ _)) e0))
      (let-match erased sc (SCCons _ _ _ _ _ _ _ _ _ _ _ _ sc1))
      (sc-get sg ns (Succ u0) j1 u v p n rest c sc1 (WE0 rest j1 v0 p0 n0 v1 p1 n1 nr1) (add-unshift j1 u0 u ad)))
    ((WE1 _ _ v0 p0 n0 v1 p1 n1 nr)
      (let-match erased nr (NthThere _ _ rest j1 _ nr1)
        ((NthHere _ _ _) (let-match erased ad (AddZero _)) (let-match erased sc (SCCons _ _ _ _ _ _ _ _ _ _ _ e1 _)) e1))
      (let-match erased sc (SCCons _ _ _ _ _ _ _ _ _ _ _ _ sc1))
      (sc-get sg ns (Succ u0) j1 u v p n rest c sc1 (WE1 rest j1 v0 p0 n0 v1 p1 n1 nr1) (add-unshift j1 u0 u ad)))))

(def-fns _ $ (erased sign-run : (erased (Bool) sg) (erased (List (Nat)) ns) (erased (List (WR)) w) (erased (List (Bool)) l) (erased (Nat) u Pa Na)
    (erased (SC sg ns (Zero) w) sc) (subterm erased (WRun w l u Pa Na) r) (erased (Mem (Nat) u ns) mu) -> (erased (SgW sg Pa Na) sw))
  (let-match erased r (WRCons _ l1 u1 Pq1 Nq1 _ p n _ _ c r1 e ap an)
    ((WRNil _) (match erased sg _ ((BFalse) (SgN (Zero) (Zero) (Zero) (AddZero (Zero)))) ((BTrue) (SgP (Zero) (Zero) (Zero) (AddZero (Zero)))))))
  (let-match erased (sc-get sg ns (Zero) u1 u1 u p n w c sc e (add-zero-right u1)) (ECIn _ _ _ _ _ _ swe mu1)
    (absurd (ECOut _ _ _ _ _ _ ni) (notin-mem u ns ni mu)))
  (let ((erased sw1)) (sign-run sg ns w l1 u1 Pq1 Nq1 sc r1 mu1))
  (match erased swe _
    ((SgN _ _ f a)
      (let-match erased sw1 (SgN _ _ f1 a1))
      (let ((erased u2) (erased v2) (erased x1) (erased _) (erased x3)) (add-ic Pq1 f1 p f Nq1 n Na a1 a an))
      (let-match erased (add-fn Pq1 p u2 Pa x1 ap) (Refl _ _))
      (SgN Pa Na v2 x3))
    ((SgP _ _ f a)
      (let-match erased sw1 (SgP _ _ f1 a1))
      (let ((erased u2) (erased v2) (erased x1) (erased _) (erased x3)) (add-ic Nq1 f1 n f Pq1 p Pa a1 a ap))
      (let-match erased (add-fn Nq1 n u2 Na x1 an) (Refl _ _))
      (SgP Pa Na v2 x3))))

(def-adts
  ((GeL : ((Ord) g) -> Type)
    enum
    (many GL0 : -> (GeL (OEq)))
    (many GL1 : -> (GeL (OGe)))))

(def-adts
  ((LeL : ((Ord) g) -> Type)
    enum
    (many LL0 : -> (LeL (OEq)))
    (many LL1 : -> (LeL (OLe)))))

(def-adts
  ((Cover : ((List (Nat)) nl) ((List (Nat)) pl) ((List (Nat)) nr) ((List (Nat)) pr) ((List (AE)) S) ((AE) b) -> Type)
    enum
    (many CvIn : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (AE) b) (erased (Mem (AE) b S) mb) -> (Cover nl pl nr pr S b))
    (many CvNorm : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn) (erased (Ord) g)
       (erased (Cover nl pl nr pr S (MkAE l r m s dp dn g)) cv) -> (Cover nl pl nr pr S (MkAE l r m s (Succ dp) (Succ dn) g)))
    (many CvGe : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn)
       (erased (Cover nl pl nr pr S (MkAE l r m s dp dn (OGe))) cv) -> (Cover nl pl nr pr S (MkAE l r m s dp dn (OEq))))
    (many CvLe : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn)
       (erased (Cover nl pl nr pr S (MkAE l r m s dp dn (OLe))) cv) -> (Cover nl pl nr pr S (MkAE l r m s dp dn (OEq))))
    (many CvDec : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn)
       (erased (Cover nl pl nr pr S (MkAE l r m s dp (Succ dn) (OGe))) cv) -> (Cover nl pl nr pr S (MkAE l r m s dp dn (OGe))))
    (many CvInc : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn)
       (erased (Cover nl pl nr pr S (MkAE l r m s (Succ dp) dn (OLe))) cv) -> (Cover nl pl nr pr S (MkAE l r m s dp dn (OLe))))
    (many CvSpG : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn)
       (erased (Cover nl pl nr pr S (MkAE l r m s dp dn (OEq))) c0) (erased (Cover nl pl nr pr S (MkAE l r m s (Succ dp) dn (OGe))) c1)
       -> (Cover nl pl nr pr S (MkAE l r m s dp dn (OGe))))
    (many CvSpL : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn)
       (erased (Cover nl pl nr pr S (MkAE l r m s dp dn (OEq))) c0) (erased (Cover nl pl nr pr S (MkAE l r m s dp (Succ dn) (OLe))) c1)
       -> (Cover nl pl nr pr S (MkAE l r m s dp dn (OLe))))
    (many CvSgN : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp) (erased (Ord) g)
       (erased (GeL g) gl) (erased (Mem (Nat) l nl) ml) (erased (Mem (Nat) r nr) mr) -> (Cover nl pl nr pr S (MkAE l r m s (Succ dp) (Zero) g)))
    (many CvSgP : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dn) (erased (Ord) g)
       (erased (LeL g) gl) (erased (Mem (Nat) l pl) ml) (erased (Mem (Nat) r pr) mr) -> (Cover nl pl nr pr S (MkAE l r m s (Zero) (Succ dn) g)))))

(def-fns _ $ (erased absurd sg-neg : (erased (Nat) Pt Nt Xt Yt dp e) (erased (Add Pt e Nt) pn) (erased (Add Pt (Zero) Xt) px)
    (erased (Add Nt (Succ dp) Yt) ny) (erased (Lt Yt (Succ Xt)) yx) -> (erased (False) f))
  (let-match erased (add-fn Pt (Zero) Xt Pt px (add-zero-right Pt)) (Refl _ _))
  (lt-asym Nt Pt (lt-le-trans Nt Yt Pt (add-pos-lt Nt (Succ dp) Yt ny (LtZ dp)) yx) (add-le-left Pt e Nt pn)))

(def-fns _ $ (erased cover-ok : (erased (List (WR)) wl wr) (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (AE) b) (erased (Conf) c)
    (erased (SC (BFalse) nl (Zero) wl) snl) (erased (SC (BTrue) pl (Zero) wl) spl) (erased (SC (BFalse) nr (Zero) wr) snr) (erased (SC (BTrue) pr (Zero) wr) spr)
    (subterm erased (Cover nl pl nr pr S b) cv) (erased (Gam wl wr b c) gm) -> (erased (AE) a) (erased (Mem (AE) a S) ma) (erased (Gam wl wr a c) ga))
  (match erased cv _
    ((CvIn _ _ _ _ _ _ mb) (values b mb gm))
    ((CvNorm _ _ _ _ _ l r m s dp dn g cv1)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
      (let ((erased x1) (erased ex) (erased ax1)) (add-succ-right-inv Pt dn Xt ax))
      (let-match erased ex (Refl _ _))
      (let ((erased y1) (erased ey) (erased ay1)) (add-succ-right-inv Nt dp Yt ay))
      (let-match erased ey (Refl _ _))
      (let ((erased rel1))
        (match erased rel (((Rel g x1 y1) rel1))
          ((REq _) (REq x1))
          ((RGe _ _ e p) (let-match erased p (AddSucc _ _ _ p1)) (RGe x1 y1 e p1))
          ((RLe _ _ e p) (let-match erased p (AddSucc _ _ _ p1)) (RLe x1 y1 e p1))))
      (cover-ok wl wr nl pl nr pr S _ c snl spl snr spr cv1 (MkGam wl wr l r m s dp dn g lt rt Pl Nl Pr Nr Pt Nt x1 y1 rl rr ap an ax1 ay1 rel1)))
    ((CvGe _ _ _ _ _ l r m s dp dn cv1)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
      (let-match erased rel (REq _))
      (cover-ok wl wr nl pl nr pr S _ c snl spl snr spr cv1
        (MkGam wl wr l r m s dp dn (OGe) lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay (RGe Xt Xt (Zero) (add-zero-right Xt)))))
    ((CvLe _ _ _ _ _ l r m s dp dn cv1)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
      (let-match erased rel (REq _))
      (cover-ok wl wr nl pl nr pr S _ c snl spl snr spr cv1
        (MkGam wl wr l r m s dp dn (OLe) lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay (RLe Xt Xt (Zero) (add-zero-right Xt)))))
    ((CvDec _ _ _ _ _ l r m s dp dn cv1)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
      (let-match erased rel (RGe _ _ e p))
      (cover-ok wl wr nl pl nr pr S _ c snl spl snr spr cv1
        (MkGam wl wr l r m s dp (Succ dn) (OGe) lt rt Pl Nl Pr Nr Pt Nt (Succ Xt) Yt rl rr ap an (add-succ-right Pt dn Xt ax) ay
          (RGe (Succ Xt) Yt (Succ e) (add-succ-right Yt e Xt p)))))
    ((CvInc _ _ _ _ _ l r m s dp dn cv1)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
      (let-match erased rel (RLe _ _ e p))
      (cover-ok wl wr nl pl nr pr S _ c snl spl snr spr cv1
        (MkGam wl wr l r m s (Succ dp) dn (OLe) lt rt Pl Nl Pr Nr Pt Nt Xt (Succ Yt) rl rr ap an ax (add-succ-right Nt dp Yt ay)
          (RLe Xt (Succ Yt) (Succ e) (add-succ-right Xt e Yt p)))))
    ((CvSpG _ _ _ _ _ l r m s dp dn c0 c1)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
      (let-match erased rel (RGe _ _ e p))
      (let-match erased e (Succ e1)
        ((Zero)
          (let-match erased (add-fn Yt (Zero) Xt Yt p (add-zero-right Yt)) (Refl _ _))
          (cover-ok wl wr nl pl nr pr S _ c snl spl snr spr c0 (MkGam wl wr l r m s dp dn (OEq) lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay (REq Xt)))))
      (cover-ok wl wr nl pl nr pr S _ c snl spl snr spr c1
        (MkGam wl wr l r m s (Succ dp) dn (OGe) lt rt Pl Nl Pr Nr Pt Nt Xt (Succ Yt) rl rr ap an ax (add-succ-right Nt dp Yt ay)
          (RGe Xt (Succ Yt) e1 (add-shift Yt e1 Xt p)))))
    ((CvSpL _ _ _ _ _ l r m s dp dn c0 c1)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
      (let-match erased rel (RLe _ _ e p))
      (let-match erased e (Succ e1)
        ((Zero)
          (let-match erased (add-fn Xt (Zero) Yt Xt p (add-zero-right Xt)) (Refl _ _))
          (cover-ok wl wr nl pl nr pr S _ c snl spl snr spr c0 (MkGam wl wr l r m s dp dn (OEq) lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay (REq Xt)))))
      (cover-ok wl wr nl pl nr pr S _ c snl spl snr spr c1
        (MkGam wl wr l r m s dp (Succ dn) (OLe) lt rt Pl Nl Pr Nr Pt Nt (Succ Xt) Yt rl rr ap an (add-succ-right Pt dn Xt ax) ay
          (RLe (Succ Xt) Yt e1 (add-shift Xt e1 Yt p)))))
    (absurd (CvSgN _ _ _ _ _ l r _ _ dp _ gl ml mr)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
      (let-match erased (sign-run (BFalse) nl wl lt l Pl Nl snl rl ml) (SgN _ _ e1 a1))
      (let-match erased (sign-run (BFalse) nr wr rt r Pr Nr snr rr mr) (SgN _ _ e2 a2))
      (let ((erased u) (erased v) (erased x1) (erased _) (erased x3)) (add-ic Pl e1 Pr e2 Nl Nr Nt a1 a2 an))
      (let-match erased (add-fn Pl Pr u Pt x1 ap) (Refl _ _))
      (let ((erased yx))
        (match erased gl (((Lt Yt (Succ Xt)) yx))
          ((GL0) (let-match erased rel (REq _)) (lt-succ Xt))
          ((GL1) (let-match erased rel (RGe _ _ e3 p)) (add-le-left Yt e3 Xt p))))
      (sg-neg Pt Nt Xt Yt dp v x3 ax ay yx))
    (absurd (CvSgP _ _ _ _ _ l r _ _ dn _ gl ml mr)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
      (let-match erased (sign-run (BTrue) pl wl lt l Pl Nl spl rl ml) (SgP _ _ e1 a1))
      (let-match erased (sign-run (BTrue) pr wr rt r Pr Nr spr rr mr) (SgP _ _ e2 a2))
      (let ((erased u) (erased v) (erased x1) (erased _) (erased x3)) (add-ic Nl e1 Nr e2 Pl Pr Pt a1 a2 ap))
      (let-match erased (add-fn Nl Nr u Nt x1 an) (Refl _ _))
      (let ((erased xy))
        (match erased gl (((Lt Xt (Succ Yt)) xy))
          ((LL0) (let-match erased rel (REq _)) (lt-succ Xt))
          ((LL1) (let-match erased rel (RLe _ _ e3 p)) (add-le-left Xt e3 Yt p))))
      (sg-neg Nt Pt Yt Xt dn v x3 ay ax xy))))

(def-adts $ (CS : -> Type)
  enum
  (many MkCS : (many (List (Nat)) nl pl nr pr) (many (List (AE)) S) -> (CS)))

(def-adts $ (Ctx : -> Type)
  enum
  (many MkCtx : (many (Bool) side) (many (Nat) y x2 s2 t1 t2) (many (Ord) g) -> (Ctx)))

(def-adts
  ((AEOf : ((Bool) side) ((Nat) x2) ((Nat) u) ((Bool) c) ((Nat) s2) ((Nat) dp) ((Nat) dn) ((Ord) g) ((AE) e) -> Type)
    enum
    (many AER : (erased (Nat) x2 u) (erased (Bool) c) (erased (Nat) s2 dp dn) (erased (Ord) g)
       -> (AEOf (BTrue) x2 u c s2 dp dn g (MkAE x2 u c s2 dp dn g)))
    (many AEL : (erased (Nat) x2 u) (erased (Bool) c) (erased (Nat) s2 dp dn) (erased (Ord) g)
       -> (AEOf (BFalse) x2 u c s2 dp dn g (MkAE u x2 c s2 dp dn g)))))

(def-adts
  ((PC : ((CS) cs) ((Ctx) cx) ((Nat) u) ((Bool) c) ((Nat) v) ((Nat) p) ((Nat) n) -> Type)
    enum
    (many PCNo : (erased (CS) cs) (erased (Bool) side) (erased (Nat) y x2 s2 t1 t2) (erased (Ord) g) (erased (Nat) u) (erased (Bool) c) (erased (Nat) v p n)
       (erased (Apart (Nat) Lt v y) ap) -> (PC cs (MkCtx side y x2 s2 t1 t2 g) u c v p n))
    (many PCYes : (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Bool) side) (erased (Nat) y x2 s2 t1 t2) (erased (Ord) g)
       (erased (Nat) u) (erased (Bool) c) (erased (Nat) p n dp2 dn2) (erased (AE) e) (erased (Add t1 n dp2) a1) (erased (Add t2 p dn2) a2)
       (erased (AEOf side x2 u c s2 dp2 dn2 g e) ae) (erased (Cover nl pl nr pr S e) cv)
       -> (PC (MkCS nl pl nr pr S) (MkCtx side y x2 s2 t1 t2 g) u c y p n))))

(def-adts
  ((Pred : ((CS) cs) ((Ctx) cx) ((Nat) u) ((List (WR)) ws) -> Type)
    enum
    (many PdNil : (erased (CS) cs) (erased (Ctx) cx) (erased (Nat) u) -> (Pred cs cx u (Nil (WR))))
    (many PdCons : (erased (CS) cs) (erased (Ctx) cx) (erased (Nat) u v0 p0 n0 v1 p1 n1) (erased (List (WR)) ws)
       (erased (PC cs cx u (BFalse) v0 p0 n0) c0) (erased (PC cs cx u (BTrue) v1 p1 n1) c1) (erased (Pred cs cx (Succ u) ws) rest)
       -> (Pred cs cx u (Cons (WR) (MkWR v0 p0 n0 v1 p1 n1) ws)))))

(def-fns _ $ (erased pred-get : (erased (CS) cs) (erased (Ctx) cx) (erased (Nat) u0 j u v p n) (subterm erased (List (WR)) ws) (erased (Bool) c)
    (erased (Pred cs cx u0 ws) pr) (erased (WEdge ws j c v p n) we) (erased (Add j u0 u) ad) -> (erased (PC cs cx u c v p n) pc))
  (match erased we _
    ((WE0 _ _ v0 p0 n0 v1 p1 n1 nr)
      (let-match erased nr (NthThere _ _ rest j1 _ nr1)
        ((NthHere _ _ _) (let-match erased ad (AddZero _)) (let-match erased pr (PdCons _ _ _ _ _ _ _ _ _ _ c0 _ _)) c0))
      (let-match erased pr (PdCons _ _ _ _ _ _ _ _ _ _ _ _ pr1))
      (pred-get cs cx (Succ u0) j1 u v p n rest c pr1 (WE0 rest j1 v0 p0 n0 v1 p1 n1 nr1) (add-unshift j1 u0 u ad)))
    ((WE1 _ _ v0 p0 n0 v1 p1 n1 nr)
      (let-match erased nr (NthThere _ _ rest j1 _ nr1)
        ((NthHere _ _ _) (let-match erased ad (AddZero _)) (let-match erased pr (PdCons _ _ _ _ _ _ _ _ _ _ _ c1 _)) c1))
      (let-match erased pr (PdCons _ _ _ _ _ _ _ _ _ _ _ _ pr1))
      (pred-get cs cx (Succ u0) j1 u v p n rest c pr1 (WE1 rest j1 v0 p0 n0 v1 p1 n1 nr1) (add-unshift j1 u0 u ad)))))

(def-adts
  ((StepOK : ((List (PT)) p) ((List (WR)) wl) ((List (WR)) wr) ((CS) cs) ((AE) a) -> Type)
    enum
    (many SOR : (erased (List (PT)) p) (erased (List (WR)) wl wr) (erased (CS) cs) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn)
       (erased (Ord) g) (erased (Bool) o) (erased (Nat) s2 x2 ap an t1 t2)
       (erased (PLook p s m (Def (Mov o (DR) s2))) pl) (erased (WEdge wl l o x2 ap an) we) (erased (Add dp ap t1) a1) (erased (Add dn an t2) a2)
       (erased (Pred cs (MkCtx (BTrue) r x2 s2 t1 t2 g) (Zero) wr) pr) -> (StepOK p wl wr cs (MkAE l r m s dp dn g)))
    (many SOL : (erased (List (PT)) p) (erased (List (WR)) wl wr) (erased (CS) cs) (erased (Nat) l r) (erased (Bool) m) (erased (Nat) s dp dn)
       (erased (Ord) g) (erased (Bool) o) (erased (Nat) s2 x2 ap an t1 t2)
       (erased (PLook p s m (Def (Mov o (DL) s2))) pl) (erased (WEdge wr r o x2 ap an) we) (erased (Add dp ap t1) a1) (erased (Add dn an t2) a2)
       (erased (Pred cs (MkCtx (BFalse) l x2 s2 t1 t2 g) (Zero) wl) pr) -> (StepOK p wl wr cs (MkAE l r m s dp dn g)))))

(def-adts
  ((ACl : ((List (PT)) p) ((List (WR)) wl) ((List (WR)) wr) ((CS) cs) ((List (AE)) xs) -> Type)
    enum
    (many ACNil : (erased (List (PT)) p) (erased (List (WR)) wl wr) (erased (CS) cs) -> (ACl p wl wr cs (Nil (AE))))
    (many ACCons : (erased (List (PT)) p) (erased (List (WR)) wl wr) (erased (CS) cs) (erased (AE) a) (erased (List (AE)) xs)
       (erased (StepOK p wl wr cs a) so) (erased (ACl p wl wr cs xs) rest) -> (ACl p wl wr cs (Cons (AE) a xs)))))

(def-fns _ $ (erased acl-get : (erased (List (PT)) p) (erased (List (WR)) wl wr) (erased (CS) cs) (erased (AE) a) (erased (List (AE)) xs)
    (erased (ACl p wl wr cs xs) ac) (subterm erased (Mem (AE) a xs) ma) -> (erased (StepOK p wl wr cs a) so))
  (match erased ma _
    ((MemHere _ _ _) (let-match erased ac (ACCons _ _ _ _ _ _ so _)) so)
    ((MemThere _ _ _ rest ma1) (let-match erased ac (ACCons _ _ _ _ _ _ _ ac1)) (acl-get p wl wr cs a rest ac1 ma1))))

(def-fns _ $ (erased wpop : (erased (List (WR)) w) (erased (List (Bool)) t t2) (erased (Bool) h) (erased (Nat) r Pa Na a b c)
    (erased (WRun w t r Pa Na) rn) (erased (Pull t h t2) pp) (erased (Nth (WR) w (Zero) (MkWR (Zero) (Zero) (Zero) a b c)) z) ->
    (erased (Nat) u P3 N3 p n) (erased (WRun w t2 u P3 N3) rn2) (erased (WEdge w u h r p n) we) (erased (Add P3 p Pa) ap) (erased (Add N3 n Na) an))
  (match erased pp _
    ((PullNil)
      (let-match erased rn (WRNil _))
      (values (Zero) (Zero) (Zero) (Zero) (Zero) (WRNil w) (WE0 w (Zero) (Zero) (Zero) (Zero) a b c z) (AddZero (Zero)) (AddZero (Zero))))
    ((PullCons _ _)
      (let-match erased rn (WRCons _ _ u P3 N3 _ p n _ _ _ rn2 we ap an))
      (values u P3 N3 p n rn2 we ap an))))

(def-fns _ $ (erased wstep : (erased (List (PT)) p) (erased (List (Tr)) mm) (erased (Ext p mm) ex) (erased (List (WR)) wl wr)
    (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) za zb zc zd ze zf)
    (erased (SC (BFalse) nl (Zero) wl) snl) (erased (SC (BTrue) pl (Zero) wl) spl) (erased (SC (BFalse) nr (Zero) wr) snr) (erased (SC (BTrue) pr (Zero) wr) spr)
    (erased (Nth (WR) wl (Zero) (MkWR (Zero) (Zero) (Zero) za zb zc)) zl) (erased (Nth (WR) wr (Zero) (MkWR (Zero) (Zero) (Zero) zd ze zf)) zr)
    (erased (AE) a) (erased (Conf) c d) (erased (StepOK p wl wr (MkCS nl pl nr pr S) a) so) (erased (Gam wl wr a c) gm) (erased (Stp mm c d) st)
    -> (erased (AE) a2) (erased (Mem (AE) a2 S) ma) (erased (Gam wl wr a2 d) ga))
  (let-match erased gm (MkGam _ _ l r m s dp dn g lt rt Pl Nl Pr Nr Pt Nt Xt Yt rl rr ap an ax ay rel))
  (match erased so _
    ((SOR _ _ _ _ _ _ _ _ _ _ _ o s2 x2 ap1 an1 t1 t2 plk we1 a1 a2 prd)
      (let ((erased lk)) (ext-look p mm s m _ ex plk))
      (let-match erased st (StepR _ _ _ _ _ rt2 _ _ h2 lk2 pp)
        (absurd (StepL _ _ _ _ _ _ _ _ _ lk2 _) (look-fn mm s m _ _ lk lk2)))
      (let-match erased (look-fn mm s m _ _ lk lk2) (Refl _ _))
      (let ((erased u) (erased Pr2) (erased Nr2) (erased bp) (erased bn) (erased rr2) (erased we2) (erased bpa) (erased bna))
        (wpop wr rt rt2 h2 r Pr Nr zd ze zf rr pp zr))
      (let-match erased (pred-get (MkCS nl pl nr pr S) (MkCtx (BTrue) r x2 s2 t1 t2 g) (Zero) u u r bp bn wr h2 prd we2 (add-zero-right u))
        (PCYes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dp2 dn2 _ c1 c2 ae cv)
        (absurd (PCNo _ _ _ _ _ _ _ _ _ _ _ _ _ apr) (apart-irrefl r apr)))
      (let-match erased ae (AER _ _ _ _ _ _ _))
      (let ((erased Pl2) (erased pa1)) (add Pl ap1))
      (let ((erased Nl2) (erased na1)) (add Nl an1))
      (let ((erased Pt2) (erased pa2)) (add Pl2 Pr2))
      (let ((erased Nt2) (erased na2)) (add Nl2 Nr2))
      (let ((erased Xt2) (erased xa2)) (add Pt2 dn2))
      (let ((erased Yt2) (erased ya2)) (add Nt2 dp2))
      (let ((erased k) (erased ka)) (add ap1 an1))
      (let ((erased ex1)) (step-id Pl Pr dn Pt Xt ap1 Pl2 Pr2 bp an1 t2 dn2 Pt2 Xt2 k ap ax pa1 bpa a2 c2 pa2 xa2 ka))
      (let ((erased ey1)) (step-id Nl Nr dp Nt Yt an1 Nl2 Nr2 bn ap1 t1 dp2 Nt2 Yt2 k an ay na1 bna a1 c1 na2 ya2 (add-comm ap1 an1 k ka)))
      (cover-ok wl wr nl pl nr pr S _ _ snl spl snr spr cv
        (MkGam wl wr x2 u h2 s2 dp2 dn2 g (Cons (Bool) o lt) rt2 Pl2 Nl2 Pr2 Nr2 Pt2 Nt2 Xt2 Yt2
          (WRCons wl lt l Pl Nl x2 ap1 an1 Pl2 Nl2 o rl we1 pa1 na1) rr2 pa2 na2 xa2 ya2 (rel-add g Xt Yt k Xt2 Yt2 rel ex1 ey1))))
    ((SOL _ _ _ _ _ _ _ _ _ _ _ o s2 x2 ap1 an1 t1 t2 plk we1 a1 a2 prd)
      (let ((erased lk)) (ext-look p mm s m _ ex plk))
      (let-match erased st (StepL _ _ _ _ _ lt2 _ _ h2 lk2 pp)
        (absurd (StepR _ _ _ _ _ _ _ _ _ lk2 _) (look-fn mm s m _ _ lk lk2)))
      (let-match erased (look-fn mm s m _ _ lk lk2) (Refl _ _))
      (let ((erased u) (erased Pl2) (erased Nl2) (erased bp) (erased bn) (erased rlb) (erased we2) (erased bpa) (erased bna))
        (wpop wl lt lt2 h2 l Pl Nl za zb zc rl pp zl))
      (let-match erased (pred-get (MkCS nl pl nr pr S) (MkCtx (BFalse) l x2 s2 t1 t2 g) (Zero) u u l bp bn wl h2 prd we2 (add-zero-right u))
        (PCYes _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ dp2 dn2 _ c1 c2 ae cv)
        (absurd (PCNo _ _ _ _ _ _ _ _ _ _ _ _ _ apr) (apart-irrefl l apr)))
      (let-match erased ae (AEL _ _ _ _ _ _ _))
      (let ((erased Pr2) (erased pa1)) (add Pr ap1))
      (let ((erased Nr2) (erased na1)) (add Nr an1))
      (let ((erased Pt2) (erased pa2)) (add Pl2 Pr2))
      (let ((erased Nt2) (erased na2)) (add Nl2 Nr2))
      (let ((erased Xt2) (erased xa2)) (add Pt2 dn2))
      (let ((erased Yt2) (erased ya2)) (add Nt2 dp2))
      (let ((erased k) (erased ka)) (add ap1 an1))
      (let ((erased ex1)) (step-id Pr Pl dn Pt Xt ap1 Pr2 Pl2 bp an1 t2 dn2 Pt2 Xt2 k (add-comm Pl Pr Pt ap) ax pa1 bpa a2 c2
        (add-comm Pl2 Pr2 Pt2 pa2) xa2 ka))
      (let ((erased ey1)) (step-id Nr Nl dp Nt Yt an1 Nr2 Nl2 bn ap1 t1 dp2 Nt2 Yt2 k (add-comm Nl Nr Nt an) ay na1 bna a1 c1
        (add-comm Nl2 Nr2 Nt2 na2) ya2 (add-comm ap1 an1 k ka)))
      (cover-ok wl wr nl pl nr pr S _ _ snl spl snr spr cv
        (MkGam wl wr u x2 h2 s2 dp2 dn2 g lt2 (Cons (Bool) o rt) Pl2 Nl2 Pr2 Nr2 Pt2 Nt2 Xt2 Yt2
          rlb (WRCons wr rt r Pr Nr x2 ap1 an1 Pr2 Nr2 o rr we1 pa1 na1) pa2 na2 xa2 ya2 (rel-add g Xt Yt k Xt2 Yt2 rel ex1 ey1))))))

(def-adts
  ((WOK : ((List (PT)) p) -> Type)
    enum
    (many MkWOK : (erased (List (PT)) p) (erased (List (WR)) wl wr) (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) za zb zc zd ze zf)
       (erased (SC (BFalse) nl (Zero) wl) snl) (erased (SC (BTrue) pl (Zero) wl) spl) (erased (SC (BFalse) nr (Zero) wr) snr) (erased (SC (BTrue) pr (Zero) wr) spr)
       (erased (Nth (WR) wl (Zero) (MkWR (Zero) (Zero) (Zero) za zb zc)) zl) (erased (Nth (WR) wr (Zero) (MkWR (Zero) (Zero) (Zero) zd ze zf)) zr)
       (erased (Mem (AE) (MkAE (Zero) (Zero) (BFalse) (Zero) (Zero) (Zero) (OEq)) S) m0) (erased (ACl p wl wr (MkCS nl pl nr pr S) S) ac)
       -> (WOK p))))

(def-fns _ $ (erased absurd wacc : (erased (List (PT)) p) (erased (List (Tr)) mm) (erased (Ext p mm) ex) (erased (List (WR)) wl wr)
    (erased (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (erased (Nat) za zb zc zd ze zf)
    (erased (SC (BFalse) nl (Zero) wl) snl) (erased (SC (BTrue) pl (Zero) wl) spl) (erased (SC (BFalse) nr (Zero) wr) snr) (erased (SC (BTrue) pr (Zero) wr) spr)
    (erased (Nth (WR) wl (Zero) (MkWR (Zero) (Zero) (Zero) za zb zc)) zl) (erased (Nth (WR) wr (Zero) (MkWR (Zero) (Zero) (Zero) zd ze zf)) zr)
    (erased (ACl p wl wr (MkCS nl pl nr pr S) S) ac) (erased (AE) a) (erased (Mem (AE) a S) ma) (erased (Conf) c) (erased (Gam wl wr a c) gm)
    (erased (Nat) t) (subterm erased (HaltsAt mm c t) hs) -> (erased (False) f))
  (let ((erased so)) (acl-get p wl wr (MkCS nl pl nr pr S) a S ac ma))
  (match erased hs _
    (absurd (HStop _ q _ _ h lk)
      (let-match erased gm (MkGam _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
      (match erased so _
        (absurd (SOR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ plk _ _ _ _) (look-fn mm q h _ _ lk (ext-look p mm q h _ ex plk)))
        (absurd (SOL _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ plk _ _ _ _) (look-fn mm q h _ _ lk (ext-look p mm q h _ ex plk)))))
    (absurd (HMove _ _ d t1 st rest)
      (let ((erased a2) (erased ma2) (erased ga)) (wstep p mm ex wl wr nl pl nr pr S za zb zc zd ze zf snl spl snr spr zl zr a c d so gm st))
      (wacc p mm ex wl wr nl pl nr pr S za zb zc zd ze zf snl spl snr spr zl zr ac a2 ma2 d ga t1 rest))))

(def-fns _ $ (erased absurd never-wfar : (erased (List (PT)) p) (erased (List (Tr)) mm) (erased (WOK p) wo) (erased (Ext p mm) ex)
    (erased (Nat) t) (erased (HaltsAt mm (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t) hs) -> (erased (False) f))
  (let-match erased wo (MkWOK _ wl wr nl pl nr pr S za zb zc zd ze zf snl spl snr spr zl zr m0 ac))
  (wacc p mm ex wl wr nl pl nr pr S za zb zc zd ze zf snl spl snr spr zl zr ac _ m0 _
    (MkGam wl wr (Zero) (Zero) (BFalse) (Zero) (Zero) (Zero) (OEq) (Nil (Bool)) (Nil (Bool)) (Zero) (Zero) (Zero) (Zero) (Zero) (Zero) (Zero) (Zero)
      (WRNil wl) (WRNil wr) (AddZero (Zero)) (AddZero (Zero)) (AddZero (Zero)) (AddZero (Zero)) (REq (Zero)))
    t hs))

(def-adts $ (WCert : -> Type)
  enum
  (many MkWC : (many (Nat) maxd) (many (List (WR)) wl wr) (many (List (Nat)) nl pl nr pr) (many (List (AE)) S) -> (WCert)))

(def-adts
  ((WEdgeR : ((List (WR)) w) ((Nat) u) ((Bool) c) -> Type)
    enum
    (many WEOk : (erased (List (WR)) w) (erased (Nat) u) (erased (Bool) c) (many (Nat) v p n) (erased (WEdge w u c v p n) we) -> (WEdgeR w u c))
    (many WENo : (erased (List (WR)) w) (erased (Nat) u) (erased (Bool) c) -> (WEdgeR w u c))))

(def-fns _ $ (many wedge-of : (erased (List (WR)) w) (many (AV (WR) w) W) (many (Nat) u) (many (Bool) c) -> (many (WEdgeR w u c) r))
  (let-match many (aget _ _ W u) (NOk _ _ _ row nr) ((NNo _ _ _) (WENo w u c)))
  (let-match many row (MkWR v0 p0 n0 v1 p1 n1))
  (match many c _
    ((BFalse) (WEOk w u c v0 p0 n0 (WE0 w u v0 p0 n0 v1 p1 n1 nr)))
    ((BTrue) (WEOk w u c v1 p1 n1 (WE1 w u v0 p0 n0 v1 p1 n1 nr)))))

(def-fns _ $ (many sgw-of : (many (Bool) sg) (many (Nat) p n) -> (many (Res (SgW sg p n)) r))
  (match many sg _
    ((BFalse)
      (let-match many (lt-dec p (Succ n)) (Yes _ _ _ _ le) ((No _ _ _ _ _) (RFail _)))
      (let ((erased f) (erased a)) (sub n p le))
      (ROk _ (SgN p n f a)))
    ((BTrue)
      (let-match many (lt-dec n (Succ p)) (Yes _ _ _ _ le) ((No _ _ _ _ _) (RFail _)))
      (let ((erased f) (erased a)) (sub p n le))
      (ROk _ (SgP p n f a)))))

(def-fns _ $ (many eck-of : (many (Bool) sg) (many (List (Nat)) ns) (many (Nat) u v p n) -> (many (Res (ECk sg ns u v p n)) r))
  (let-match many (has-n v ns) (BTrue) ((BFalse) (match many (notin-of v ns) _ ((ROk _ ni) (ROk _ (ECOut sg ns u v p n ni))) ((RFail _) (RFail _)))))
  (let-match many (sgw-of sg p n) (ROk _ sw) ((RFail _) (RFail _)))
  (let-match many (mem-n u ns) (ROk _ mu) ((RFail _) (RFail _)))
  (ROk _ (ECIn sg ns u v p n sw mu)))

(def-fns _ $ (many sc-of : (many (Bool) sg) (many (List (Nat)) ns) (many (Nat) u) (subterm many (List (WR)) ws) -> (many (Res (SC sg ns u ws)) r))
  (let-match many ws (Cons _ row rest) ((Nil _) (ROk _ (SCNil sg ns u))))
  (let-match many row (MkWR v0 p0 n0 v1 p1 n1))
  (let-match many (eck-of sg ns u v0 p0 n0) (ROk _ e0) ((RFail _) (RFail _)))
  (let-match many (eck-of sg ns u v1 p1 n1) (ROk _ e1) ((RFail _) (RFail _)))
  (let-match many (notail $ sc-of sg ns (Succ u) rest) (ROk _ sc) ((RFail _) (RFail _)))
  (ROk _ (SCCons sg ns u v0 p0 n0 v1 p1 n1 rest e0 e1 sc)))

(def-fns _ $ (many ord-eq : (many (Ord) a b) -> (many (Maybe (Eq (Ord) a b)) r))
  (match many a _
    ((OEq) (match many b _ ((OEq) (Some _ (Refl (Ord) a))) (else (None _))))
    ((OGe) (match many b _ ((OGe) (Some _ (Refl (Ord) a))) (else (None _))))
    ((OLe) (match many b _ ((OLe) (Some _ (Refl (Ord) a))) (else (None _))))))

(def-fns _ $ (many eq-ae : (many (AE) a b) -> (many (Maybe (Eq (AE) a b)) r))
  (let-match many a (MkAE l1 r1 m1 s1 p1 n1 g1))
  (let-match many b (MkAE l2 r2 m2 s2 p2 n2 g2))
  (let-match many (eq-nat l1 l2) (Some _ e1) ((None _) (None _)))
  (let-match erased e1 (Refl _ _))
  (let-match many (eq-nat r1 r2) (Some _ e2) ((None _) (None _)))
  (let-match erased e2 (Refl _ _))
  (let-match many (eq-bit m1 m2) (Some _ e3) ((None _) (None _)))
  (let-match erased e3 (Refl _ _))
  (let-match many (eq-nat s1 s2) (Some _ e4) ((None _) (None _)))
  (let-match erased e4 (Refl _ _))
  (let-match many (eq-nat p1 p2) (Some _ e5) ((None _) (None _)))
  (let-match erased e5 (Refl _ _))
  (let-match many (eq-nat n1 n2) (Some _ e6) ((None _) (None _)))
  (let-match erased e6 (Refl _ _))
  (let-match many (ord-eq g1 g2) (Some _ e7) ((None _) (None _)))
  (let-match erased e7 (Refl _ _))
  (Some _ (Refl (AE) a)))

(def-fns _ $ (many mem-ae : (many (AE) a) (subterm many (List (AE)) xs) -> (many (Res (Mem (AE) a xs)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (RFail _)))
  (let-match many (eq-ae a x) (None _) ((Some _ e) (let-match erased e (Refl _ _)) (ROk _ (MemHere (AE) a rest))))
  (let-match many (notail $ mem-ae a rest) (ROk _ mm) ((RFail _) (RFail _)))
  (ROk _ (MemThere (AE) a x rest mm)))

(def-fns _ $ (many sgn-cover : (many (List (Nat)) nl pl nr pr) (erased (List (AE)) S) (many (AE) b) -> (many (Res (Cover nl pl nr pr S b)) r))
  (let-match many b (MkAE l r m s dp dn g))
  (match many dp _
    ((Succ dp1)
      (let-match many dn (Zero) ((Succ _) (RFail _)))
      (let ((many gl)) (match many g (((Maybe (GeL g)) x)) ((OEq) (Some _ (GL0))) ((OGe) (Some _ (GL1))) ((OLe) (None _))))
      (let-match many gl (Some _ gl1) ((None _) (RFail _)))
      (let-match many (mem-n l nl) (ROk _ ml) ((RFail _) (RFail _)))
      (let-match many (mem-n r nr) (ROk _ mr) ((RFail _) (RFail _)))
      (ROk _ (CvSgN nl pl nr pr S l r m s dp1 g gl1 ml mr)))
    ((Zero)
      (let-match many dn (Succ dn1) ((Zero) (RFail _)))
      (let ((many gl)) (match many g (((Maybe (LeL g)) x)) ((OEq) (Some _ (LL0))) ((OLe) (Some _ (LL1))) ((OGe) (None _))))
      (let-match many gl (Some _ gl1) ((None _) (RFail _)))
      (let-match many (mem-n l pl) (ROk _ ml) ((RFail _) (RFail _)))
      (let-match many (mem-n r pr) (ROk _ mr) ((RFail _) (RFail _)))
      (ROk _ (CvSgP nl pl nr pr S l r m s dn1 g gl1 ml mr)))))

(def-fns _
  ((many cover-of : (many (List (Nat)) nl pl nr pr) (many (List (AE)) S) (many (Nat) maxd) (subterm many (Nat) fuel) (many (AE) b)
       -> (many (Res (Cover nl pl nr pr S b)) r))
    (let-match many fuel (Succ f) ((Zero) (RFail _)))
    (let-match many b (MkAE l r m s dp dn g))
    (let ((many norm))
      (match many dp (((Maybe (Res (Cover nl pl nr pr S b))) x))
        ((Succ dp1)
          (match many dn (((Maybe (Res (Cover nl pl nr pr S b))) x))
            ((Succ dn1)
              (Some _ (match many (notail $ cover-of nl pl nr pr S maxd f (MkAE l r m s dp1 dn1 g)) _
                ((ROk _ c) (ROk _ (CvNorm nl pl nr pr S l r m s dp1 dn1 g c)))
                ((RFail _) (RFail _)))))
            ((Zero) (None _))))
        ((Zero) (None _))))
    (let-match many norm (None _) ((Some _ x) x))
    (match many (sgn-cover nl pl nr pr S b) _
      ((ROk _ c) (ROk _ c))
      ((RFail _) (tail $ cover-rest nl pl nr pr S maxd f b))))
  ((many cover-rest : (many (List (Nat)) nl pl nr pr) (many (List (AE)) S) (many (Nat) maxd) (subterm many (Nat) fuel) (many (AE) b)
       -> (many (Res (Cover nl pl nr pr S b)) r))
    (let-match many (mem-ae b S) (RFail _) ((ROk _ mb) (ROk _ (CvIn nl pl nr pr S b mb))))
    (let-match many fuel (Succ f) ((Zero) (RFail _)))
    (let-match many b (MkAE l r m s dp dn g))
    (let ((many ad) (erased _)) (add dp dn))
    (let ((many c)) (nat-cmp ad maxd))
    (match many g _
      ((OEq)
        (let-match many c (CLt _ _ _ _ _) (else
          (match many dp _
            ((Succ _) (match many (notail $ cover-of nl pl nr pr S maxd f (MkAE l r m s dp dn (OGe))) _ ((ROk _ cv) (ROk _ (CvGe nl pl nr pr S l r m s dp dn cv))) ((RFail _) (RFail _))))
            ((Zero)
              (let-match many dn (Succ _) ((Zero) (RFail _)))
              (match many (notail $ cover-of nl pl nr pr S maxd f (MkAE l r m s dp dn (OLe))) _ ((ROk _ cv) (ROk _ (CvLe nl pl nr pr S l r m s dp dn cv))) ((RFail _) (RFail _)))))))
        (RFail _))
      ((OGe)
        (match many c _
          ((CGt _ _ _ _ _) (match many (notail $ cover-of nl pl nr pr S maxd f (MkAE l r m s dp (Succ dn) (OGe))) _
            ((ROk _ cv) (ROk _ (CvDec nl pl nr pr S l r m s dp dn cv))) ((RFail _) (RFail _))))
          ((CLt _ _ _ _ _)
            (let-match many (notail $ cover-of nl pl nr pr S maxd f (MkAE l r m s dp dn (OEq))) (ROk _ c0) ((RFail _) (RFail _)))
            (let-match many (notail $ cover-of nl pl nr pr S maxd f (MkAE l r m s (Succ dp) dn (OGe))) (ROk _ c1) ((RFail _) (RFail _)))
            (ROk _ (CvSpG nl pl nr pr S l r m s dp dn c0 c1)))
          ((CEq _ _ _) (RFail _))))
      ((OLe)
        (match many c _
          ((CGt _ _ _ _ _) (match many (notail $ cover-of nl pl nr pr S maxd f (MkAE l r m s (Succ dp) dn (OLe))) _
            ((ROk _ cv) (ROk _ (CvInc nl pl nr pr S l r m s dp dn cv))) ((RFail _) (RFail _))))
          ((CLt _ _ _ _ _)
            (let-match many (notail $ cover-of nl pl nr pr S maxd f (MkAE l r m s dp dn (OEq))) (ROk _ c0) ((RFail _) (RFail _)))
            (let-match many (notail $ cover-of nl pl nr pr S maxd f (MkAE l r m s dp (Succ dn) (OLe))) (ROk _ c1) ((RFail _) (RFail _)))
            (ROk _ (CvSpL nl pl nr pr S l r m s dp dn c0 c1)))
          ((CEq _ _ _) (RFail _)))))))

(def-fns _ $ (many pc-of : (many (List (Nat)) nl pl nr pr) (many (List (AE)) S) (many (Nat) maxd) (many (Bool) side) (many (Nat) y x2 s2 t1 t2) (many (Ord) g)
    (many (Nat) u) (many (Bool) c) (many (Nat) v p n) -> (many (Res (PC (MkCS nl pl nr pr S) (MkCtx side y x2 s2 t1 t2 g) u c v p n)) r))
  (let-match many (nat-eq v y) (Equal _ _ _) ((Unequal _ _ _ _ ap) (ROk _ (PCNo (MkCS nl pl nr pr S) side y x2 s2 t1 t2 g u c v p n ap))))
  (let ((many dp2) (erased a1)) (add t1 n))
  (let ((many dn2) (erased a2)) (add t2 p))
  (let ((many e) (erased ae))
    (match many side (((AE) e) ((AEOf side x2 u c s2 dp2 dn2 g e) ae))
      ((BTrue) (values (MkAE x2 u c s2 dp2 dn2 g) (AER x2 u c s2 dp2 dn2 g)))
      ((BFalse) (values (MkAE u x2 c s2 dp2 dn2 g) (AEL x2 u c s2 dp2 dn2 g)))))
  (let-match many (cover-of nl pl nr pr S maxd 64 e) (ROk _ cv) ((RFail _) (RFail _)))
  (ROk _ (PCYes nl pl nr pr S side y x2 s2 t1 t2 g u c p n dp2 dn2 e a1 a2 ae cv)))

(def-fns _ $ (many pred-of : (many (List (Nat)) nl pl nr pr) (many (List (AE)) S) (many (Nat) maxd) (many (Bool) side) (many (Nat) y x2 s2 t1 t2) (many (Ord) g)
    (many (Nat) u) (subterm many (List (WR)) ws) -> (many (Res (Pred (MkCS nl pl nr pr S) (MkCtx side y x2 s2 t1 t2 g) u ws)) r))
  (let-match many ws (Cons _ row rest) ((Nil _) (ROk _ (PdNil _ _ u))))
  (let-match many row (MkWR v0 p0 n0 v1 p1 n1))
  (let-match many (pc-of nl pl nr pr S maxd side y x2 s2 t1 t2 g u (BFalse) v0 p0 n0) (ROk _ c0) ((RFail _) (RFail _)))
  (let-match many (pc-of nl pl nr pr S maxd side y x2 s2 t1 t2 g u (BTrue) v1 p1 n1) (ROk _ c1) ((RFail _) (RFail _)))
  (let-match many (notail $ pred-of nl pl nr pr S maxd side y x2 s2 t1 t2 g (Succ u) rest) (ROk _ pr1) ((RFail _) (RFail _)))
  (ROk _ (PdCons _ _ u v0 p0 n0 v1 p1 n1 rest c0 c1 pr1)))

(def-fns _ $ (many step-of : (many (List (PT)) p) (many (List (WR)) wl wr) (many (AV (WR) wl) WL) (many (AV (WR) wr) WRa)
    (many (List (Nat)) nl pl nr pr) (many (List (AE)) S) (many (Nat) maxd) (many (AE) a) -> (many (Res (StepOK p wl wr (MkCS nl pl nr pr S) a)) res))
  (let-match many a (MkAE l r m s dp dn g))
  (let-match many (plook p s m) (PLOk _ _ _ x plk) ((PLNo _ _ _) (RFail _)))
  (let-match many x (Def t) ((Undef) (RFail _)))
  (let-match many t (Mov o d s2) ((Hlt) (RFail _)))
  (match many d _
    ((DR)
      (let-match many (wedge-of wl WL l o) (WEOk _ _ _ x2 ap an we) ((WENo _ _ _) (RFail _)))
      (let ((many t1) (erased a1)) (add dp ap))
      (let ((many t2) (erased a2)) (add dn an))
      (let-match many (pred-of nl pl nr pr S maxd (BTrue) r x2 s2 t1 t2 g 0 wr) (ROk _ prd) ((RFail _) (RFail _)))
      (ROk _ (SOR p wl wr _ l r m s dp dn g o s2 x2 ap an t1 t2 plk we a1 a2 prd)))
    ((DL)
      (let-match many (wedge-of wr WRa r o) (WEOk _ _ _ x2 ap an we) ((WENo _ _ _) (RFail _)))
      (let ((many t1) (erased a1)) (add dp ap))
      (let ((many t2) (erased a2)) (add dn an))
      (let-match many (pred-of nl pl nr pr S maxd (BFalse) l x2 s2 t1 t2 g 0 wl) (ROk _ prd) ((RFail _) (RFail _)))
      (ROk _ (SOL p wl wr _ l r m s dp dn g o s2 x2 ap an t1 t2 plk we a1 a2 prd)))))

(def-fns _ $ (many acl-of : (many (List (PT)) p) (many (List (WR)) wl wr) (many (AV (WR) wl) WL) (many (AV (WR) wr) WRa)
    (many (List (Nat)) nl pl nr pr) (many (List (AE)) S) (many (Nat) maxd) (subterm many (List (AE)) xs) -> (many (Res (ACl p wl wr (MkCS nl pl nr pr S) xs)) res))
  (let-match many xs (Cons _ a rest) ((Nil _) (ROk _ (ACNil p wl wr _))))
  (let-match many (step-of p wl wr WL WRa nl pl nr pr S maxd a) (ROk _ so) ((RFail _) (RFail _)))
  (let-match many (notail $ acl-of p wl wr WL WRa nl pl nr pr S maxd rest) (ROk _ ac) ((RFail _) (RFail _)))
  (ROk _ (ACCons p wl wr _ a rest so ac)))

(def-fns _ $ (many check-wfar : (many (List (PT)) p) (many (WCert) ct) -> (many (Res (WOK p)) res))
  (let-match many ct (MkWC maxd wl wr nl pl nr pr S))
  (let ((many WL)) (mk-av _ wl))
  (let ((many WRa)) (mk-av _ wr))
  (let-match many (aget _ _ WL 0) (NOk _ _ _ rl zl) ((NNo _ _ _) (RFail _)))
  (let-match many rl (MkWR la lb lc za zb zc))
  (let-match many la (Zero) ((Succ _) (RFail _)))
  (let-match many lb (Zero) ((Succ _) (RFail _)))
  (let-match many lc (Zero) ((Succ _) (RFail _)))
  (let-match many (aget _ _ WRa 0) (NOk _ _ _ rr zr) ((NNo _ _ _) (RFail _)))
  (let-match many rr (MkWR ra rb rc zd ze zf))
  (let-match many ra (Zero) ((Succ _) (RFail _)))
  (let-match many rb (Zero) ((Succ _) (RFail _)))
  (let-match many rc (Zero) ((Succ _) (RFail _)))
  (let-match many (sc-of (BFalse) nl 0 wl) (ROk _ snl) ((RFail _) (RFail _)))
  (let-match many (sc-of (BTrue) pl 0 wl) (ROk _ spl) ((RFail _) (RFail _)))
  (let-match many (sc-of (BFalse) nr 0 wr) (ROk _ snr) ((RFail _) (RFail _)))
  (let-match many (sc-of (BTrue) pr 0 wr) (ROk _ spr) ((RFail _) (RFail _)))
  (let-match many (mem-ae (MkAE 0 0 (BFalse) 0 0 0 (OEq)) S) (ROk _ m0) ((RFail _) (RFail _)))
  (let-match many (acl-of p wl wr WL WRa nl pl nr pr S maxd S) (ROk _ ac) ((RFail _) (RFail _)))
  (ROk _ (MkWOK p wl wr nl pl nr pr S za zb zc zd ze zf snl spl snr spr zl zr m0 ac)))

(def-fns _ $ (many wrow : (many (List (WR)) w) (many (Nat) u) (many (Bool) c) -> (many (Nat) v p n))
  (let-match many (nth-opt _ w u) (Some _ row) ((None _) (values 0 0 0)))
  (let-match many row (MkWR v0 p0 n0 v1 p1 n1))
  (match many c _ ((BFalse) (values v0 p0 n0)) ((BTrue) (values v1 p1 n1))))

(def-fns _ $ (many bad-edge : (many (Bool) sg) (many (Nat) p n) -> (many (Bool) b))
  (match many sg _
    ((BFalse) (match many (lt-dec n p) _ ((Yes _ _ _ _ _) (BTrue)) ((No _ _ _ _ _) (BFalse))))
    ((BTrue) (match many (lt-dec p n) _ ((Yes _ _ _ _ _) (BTrue)) ((No _ _ _ _ _) (BFalse))))))

(def-fns _ $ (many bad-round : (many (Bool) sg) (many (Nat) u) (subterm many (List (WR)) ws) (many (List (Nat)) bad) -> (many (List (Nat)) r))
  (let-match many ws (Cons _ row rest) ((Nil _) bad))
  (let-match many row (MkWR v0 p0 n0 v1 p1 n1))
  (let ((many ub)) (has-n u bad))
  (let ((many e0)) (match many ub (((Bool) x)) ((BTrue) (BTrue)) ((BFalse) (bad-edge sg p0 n0))))
  (let ((many e1)) (match many ub (((Bool) x)) ((BTrue) (BTrue)) ((BFalse) (bad-edge sg p1 n1))))
  (let ((many b1)) (match many e0 (((List (Nat)) x)) ((BTrue) (union-n (Cons _ v0 (Nil _)) bad)) ((BFalse) bad)))
  (let ((many b2)) (match many e1 (((List (Nat)) x)) ((BTrue) (union-n (Cons _ v1 (Nil _)) b1)) ((BFalse) b1)))
  (tail $ bad-round sg (Succ u) rest b2))

(def-fns _ $ (many bad-fix : (many (Bool) sg) (many (List (WR)) w) (subterm many (Nat) fuel) (many (List (Nat)) bad) -> (many (List (Nat)) r))
  (let-match many fuel (Succ f) ((Zero) bad))
  (let ((many b2)) (bad-round sg 0 w bad))
  (match many (nat-eq (len-n _ b2) (len-n _ bad)) _ ((Equal _ _ _) bad) (else (tail $ bad-fix sg w f b2))))

(def-fns _ $ (many keep-not : (subterm many (List (Nat)) xs) (many (List (Nat)) bad) -> (many (List (Nat)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil (Nat))))
  (let ((many ks)) (notail $ keep-not rest bad))
  (match many (has-n x bad) _ ((BTrue) ks) ((BFalse) (Cons _ x ks))))

(def-fns _ $ (many sign-set : (many (Bool) sg) (many (List (WR)) w) -> (many (List (Nat)) ns))
  (let ((many n)) (len-n _ w))
  (let ((many bad)) (bad-fix sg w (Succ n) (Nil (Nat))))
  (let ((many us) (erased _)) (range n))
  (tail $ keep-not us bad))


(def-fns _ $ (many norm-d : (subterm many (Nat) dp) (many (Nat) dn) -> (many (Nat) a b))
  (let-match many dp (Succ dp1) ((Zero) (values dp dn)))
  (let-match many dn (Succ dn1) ((Zero) (values dp dn)))
  (tail $ norm-d dp1 dn1))

(def-adts $ (WG : -> Type)
  enum
  (many MkWG : (many (Nat) maxd) (many (List (WR)) wl wr) (many (List (Nat)) nl pl nr pr) -> (WG)))

(def-fns _ $ (many sgn-empty : (many (WG) wg) (many (AE) b) -> (many (Bool) e))
  (let-match many wg (MkWG _ _ _ nl pl nr pr))
  (let-match many b (MkAE l r _ _ dp dn g))
  (let ((many inl)) (match many (has-n l nl) (((Bool) x)) ((BTrue) (has-n r nr)) ((BFalse) (BFalse))))
  (let ((many inp)) (match many (has-n l pl) (((Bool) x)) ((BTrue) (has-n r pr)) ((BFalse) (BFalse))))
  (let-match many dp (Zero) ((Succ _) (match many g _ ((OLe) (BFalse)) (else inl))))
  (let-match many dn (Succ _) ((Zero) (BFalse)))
  (match many g _ ((OGe) (BFalse)) (else inp)))

(def-fns _ $ (many mk-ae : (many (Nat) l r) (many (Bool) m) (many (Nat) s dp dn) (many (Ord) g) -> (many (AE) a))
  (let ((many a2) (many b2)) (norm-d dp dn))
  (MkAE l r m s a2 b2 g))

(def-fns _ $ (many simp : (many (Nat) maxd) (many (AE) b) -> (many (List (AE)) r))
  (let-match many b (MkAE l r m s dp dn g))
  (let ((many one)) (Cons _ b (Nil _)))
  (let ((many ad) (erased _)) (add dp dn))
  (let ((many c)) (nat-cmp ad maxd))
  (match many g _
    ((OEq)
      (let-match many c (CLt _ _ _ _ _) (else
        (let-match many dp (Zero) ((Succ _) (Cons _ (MkAE l r m s dp dn (OGe)) (Nil _))))
        (let-match many dn (Succ _) ((Zero) one))
        (Cons _ (MkAE l r m s dp dn (OLe)) (Nil _))))
      one)
    ((OGe)
      (match many c _
        ((CGt _ _ _ _ _) (Cons _ (mk-ae l r m s dp (Succ dn) (OGe)) (Nil _)))
        ((CLt _ _ _ _ _) (Cons _ (MkAE l r m s dp dn (OEq)) (Cons _ (mk-ae l r m s (Succ dp) dn (OGe)) (Nil _))))
        ((CEq _ _ _) one)))
    ((OLe)
      (match many c _
        ((CGt _ _ _ _ _) (Cons _ (mk-ae l r m s (Succ dp) dn (OLe)) (Nil _)))
        ((CLt _ _ _ _ _) (Cons _ (MkAE l r m s dp dn (OEq)) (Cons _ (mk-ae l r m s dp (Succ dn) (OLe)) (Nil _))))
        ((CEq _ _ _) one)))))

(def-fns _ $ (many raw-succ : (many (WG) wg) (many (Bool) side) (many (Nat) y x2 s2 t1 t2) (many (Ord) g) (many (Nat) u) (subterm many (List (WR)) ws)
    -> (many (List (AE)) r))
  (let-match many ws (Cons _ row rest) ((Nil _) (Nil _)))
  (let-match many wg (MkWG maxd _ _ _ _ _ _))
  (let-match many row (MkWR v0 p0 n0 v1 p1 n1))
  (let ((many more)) (notail $ raw-succ wg side y x2 s2 t1 t2 g (Succ u) rest))
  (let ((many one))
    (match many (nat-eq v1 y) (((List (AE)) x))
      ((Equal _ _ _)
        (let ((many dp2) (erased _)) (add t1 n1))
        (let ((many dn2) (erased _)) (add t2 p1))
        (let ((many e)) (match many side (((AE) x)) ((BTrue) (mk-ae x2 u (BTrue) s2 dp2 dn2 g)) ((BFalse) (mk-ae u x2 (BTrue) s2 dp2 dn2 g))))
        (match many (sgn-empty wg e) (((List (AE)) x)) ((BTrue) more) ((BFalse) (cat _ (simp maxd e) more))))
      (else more)))
  (let-match many (nat-eq v0 y) (Equal _ _ _) (else one))
  (let ((many dp2) (erased _)) (add t1 n0))
  (let ((many dn2) (erased _)) (add t2 p0))
  (let ((many e)) (match many side (((AE) x)) ((BTrue) (mk-ae x2 u (BFalse) s2 dp2 dn2 g)) ((BFalse) (mk-ae u x2 (BFalse) s2 dp2 dn2 g))))
  (match many (sgn-empty wg e) _ ((BTrue) one) ((BFalse) (cat _ (simp maxd e) one))))

(def-fns _ $ (many succs : (many (List (PT)) p) (many (WG) wg) (many (AE) a) -> (many (Maybe (List (AE))) r))
  (let-match many wg (MkWG _ wl wr _ _ _ _))
  (let-match many a (MkAE l r m s dp dn g))
  (let-match many (plook p s m) (PLOk _ _ _ x _) ((PLNo _ _ _) (None _)))
  (let-match many x (Def t) ((Undef) (None _)))
  (let-match many t (Mov o d s2) ((Hlt) (None _)))
  (match many d _
    ((DR)
      (let ((many x2) (many ap) (many an)) (wrow wl l o))
      (let ((many t1) (erased _)) (add dp ap))
      (let ((many t2) (erased _)) (add dn an))
      (Some _ (raw-succ wg (BTrue) r x2 s2 t1 t2 g 0 wr)))
    ((DL)
      (let ((many x2) (many ap) (many an)) (wrow wr r o))
      (let ((many t1) (erased _)) (add dp ap))
      (let ((many t2) (erased _)) (add dn an))
      (Some _ (raw-succ wg (BFalse) l x2 s2 t1 t2 g 0 wl)))))

(def-fns _ $ (many has-ae : (many (AE) a) (subterm many (List (AE)) xs) -> (many (Bool) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (BFalse)))
  (match many (eq-ae a x) _ ((Some _ _) (BTrue)) ((None _) (tail $ has-ae a rest))))

(def-fns _ $ (many add-new : (subterm many (List (AE)) xs) (many (List (AE)) S) -> (many (List (AE)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) S))
  (match many (has-ae x S) _ ((BTrue) (tail $ add-new rest S)) ((BFalse) (tail $ add-new rest (snoc _ S x)))))

(def-fns _ $ (many wbfs : (many (List (PT)) p) (many (WG) wg) (subterm many (Nat) fuel) (many (Nat) k) (many (List (AE)) S) -> (many (Maybe (List (AE))) r))
  (let-match many fuel (Succ f) ((Zero) (None _)))
  (let-match many (nth-opt _ S k) (Some _ a) ((None _) (Some _ S)))
  (let-match many (succs p wg a) (Some _ xs) ((None _) (None _)))
  (tail $ wbfs p wg f (Succ k) (add-new xs S)))

(def-fns _ $ (many wfar-gen : (many (List (PT)) p) (many (Nat) maxd) (many (List (WR)) wl wr) -> (many (WCert) ct))
  (let ((many nl)) (sign-set (BFalse) wl))
  (let ((many pl)) (sign-set (BTrue) wl))
  (let ((many nr)) (sign-set (BFalse) wr))
  (let ((many pr)) (sign-set (BTrue) wr))
  (let ((many wg)) (MkWG maxd wl wr nl pl nr pr))
  (let ((many a0)) (MkAE 0 0 (BFalse) 0 0 0 (OEq)))
  (let ((many S)) (match many (wbfs p wg 20000 0 (Cons _ a0 (Nil _))) (((List (AE)) x)) ((Some _ S) S) ((None _) (Nil _))))
  (MkWC maxd wl wr nl pl nr pr S))
