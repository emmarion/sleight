(def-adts
  ((E1 : ((List (Tk)) W) -> Type)
    enum
    (many E1O : -> (E1 (Cons (Tk) (T0) (Nil (Tk)))))
    (many E1C : (erased (Tk) t) (erased (List (Tk)) W) (erased (E1 W) p) -> (E1 (Cons (Tk) t W)))))

(def-adts
  ((D0 : ((List (Nat)) D) -> Type)
    enum
    (many D0O : -> (D0 (Cons (Nat) (Zero) (Nil (Nat)))))
    (many D0C : (erased (Nat) d e) (erased (List (Nat)) D) (erased (D0 (Cons (Nat) e D)) p) -> (D0 (Cons (Nat) d (Cons (Nat) e D))))))

(def-fns _ $ (erased d0-cons : (erased (Nat) d) (erased (List (Nat)) D) (erased (D0 D) q) -> (erased (D0 (Cons (Nat) d D)) r))
  (match erased q _
    ((D0O) (D0C d (Zero) (Nil (Nat)) q))
    ((D0C d1 e D1 _) (D0C d d1 (Cons (Nat) e D1) q))))

(def-fns _ $ (erased dg-d0 : (erased (List (Ps)) w) (erased (List (Nat)) E D) (subterm erased (Dg w E D) g) (erased (D0 E) q) -> (erased (D0 D) r))
  (match erased g _
    ((DgN _) q)
    ((DgC _ h l w1 _ D1 g1 _) (d0-cons h _ (d0-cons l D1 (dg-d0 w1 E D1 g1 q))))))

(def-fns _ $ (erased tpr-e1 : (erased (Nat) m) (erased (List (Tk)) R X) (subterm erased (TpR m R X) p) (erased (E1 R) q) -> (erased (E1 X) r))
  (match erased p _
    ((TpZ _) q)
    ((TpS m1 _ X1 p1) (E1C (Tp) X1 (tpr-e1 m1 R X1 p1 q)))))

(def-fns _ $ (erased enc-e1 : (erased (List (Nat)) D) (erased (List (Tk)) X) (subterm erased (DEnc D X) e) (erased (D0 D) q) -> (erased (E1 X) r))
  (let-match erased e (EnC d D1 X1 _ e1 t) (absurd (EnN) (match erased q _)))
  (match erased q _
    ((D0O) (let-match erased e1 (EnN)) (let-match erased t (DtZ _)) (E1O))
    ((D0C _ _ _ q1)
      (let ((erased r1)) (enc-e1 D1 X1 e1 q1))
      (match erased t _
        ((DtZ _) (E1C (T0) X1 r1))
        ((DtS k _ _ p) (tpr-e1 k _ X p (E1C (T1) X1 r1)))))))

(def-fns _ $ (erased sw-split : (erased (List (Nat)) K K2) (erased (List (Tk)) X W) (subterm erased (Sw K X (SEnd K2)) sw) (erased (Ap3 W X) a) (erased (E1 W) e)
    -> (erased (List (Nat)) K3) (erased (Sw K W (SEnd K3)) s1) (erased (Sw K3 (Cons (Tk) (Tp) $ Cons (Tk) (T1) $ Cons (Tk) (T0) $ Nil (Tk)) (SEnd K2)) s2))
  (match erased sw _
    ((SwEnd _) (match erased a _))
    ((SwT0 _ R _ p)
      (let-match erased a (A3C _ W1 _ a1))
      (match erased e _
        ((E1O) (let-match erased a1 (A3N)) (values (Cons (Nat) n2 K) (SwT0 K (Nil (Tk)) _ (SwEnd _)) p))
        ((E1C _ _ e1)
          (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n2 K) K2 R W1 p a1 e1))
          (values K3 (SwT0 K W1 _ s1) s2))))
    ((SwT1 _ R _ p)
      (let-match erased a (A3C _ W1 _ a1))
      (let-match erased e (E1C _ _ e1))
      (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n3 K) K2 R W1 p a1 e1))
      (values K3 (SwT1 K W1 _ s1) s2))
    ((SwP0 _ R _ p)
      (let-match erased a (A3C _ W1 _ a1))
      (let-match erased a1 (A3C _ W2 _ a2))
      (let-match erased e (E1C _ _ e1))
      (match erased e1 _
        ((E1O) (let-match erased a2 (A3N)) (values (Cons (Nat) n3 K) (SwP0 K (Nil (Tk)) _ (SwEnd _)) p))
        ((E1C _ _ e2)
          (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n3 K) K2 R W2 p a2 e2))
          (values K3 (SwP0 K W2 _ s1) s2))))
    ((SwP1M s0 K1 R _ p)
      (let-match erased a (A3C _ W1 _ a1) (absurd (A3N) (match erased e _)))
      (let-match erased a1 (A3C _ W2 _ a2))
      (let-match erased e (E1C _ _ e1))
      (let-match erased e1 (E1C _ _ e2))
      (let ((erased K3) (erased s1) (erased s2))
        (sw-split (Cons (Nat) n2 $ Cons (Nat) n3 $ Cons (Nat) (Succ s0) K1) K2 R W2 p a2 e2))
      (values K3 (SwP1M s0 K1 W2 _ s1) s2))
    ((SwPPM s0 K1 R _ p)
      (let-match erased a (A3C _ W1 _ a1))
      (let-match erased a1 (A3C _ W2 _ a2) (absurd (A3N) (let-match erased e (E1C _ _ e1)) (match erased e1 _)))
      (let-match erased e (E1C _ _ e1))
      (let-match erased e1 (E1C _ _ e2))
      (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n3 $ Cons (Nat) (Succ s0) K1) K2 R W2 p a2 e2))
      (values K3 (SwPPM s0 K1 W2 _ s1) s2))))

(def-adts
  ((Cx : ((List (Tk)) W Y) -> Type)
    enum
    (many MkCx : (erased (List (Tk)) W Y) (erased (Nat) s0) (erased (List (Nat)) K1)
       (erased (Sw (Cons (Nat) n3 (Nil (Nat))) W (SEnd (Cons (Nat) n2 (Cons (Nat) s0 K1)))) sw)
       (erased (Wk (Cons (Nat) n3 $ Cons (Nat) n3 $ Cons (Nat) (Succ s0) K1) (Cons (Tk) (T1) (Nil (Tk))) Y) wk) -> (Cx W Y))))

(def-fns _ $ (erased rd-contact : (erased (List (Tk)) X W Y) (erased (Tt) T2) (erased (Ap3 W X) a) (erased (E1 W) e)
    (erased (Rd (Cons (Tk) (Tp) (Cons (Tk) (T1) X)) (Tt1) Y T2 n4) rd) -> (erased (Cx W Y) cx) (erased (Eq (Tt) T2 (Tt1)) et))
  (let-match erased rd (RdE _ W2 _ K K2 _ _ _ sw en wk))
  (let ((erased K3) (erased s1) (erased s2)) (sw-split (Cons (Nat) n3 (Nil (Nat))) K X W sw a e))
  (let-match erased s2 (SwP1M s0 K1 _ _ p))
  (let-match erased p (SwT0 _ _ _ p1))
  (let-match erased p1 (SwEnd _))
  (let-match erased en (EnMP _ _ _ _))
  (values (MkCx W Y s0 K1 s1 wk) (Refl _ T2)))

(def-adts
  ((AcR : ((List (Tk)) Z Y) ((List (Bool)) r u2 zr x3) -> Type)
    enum
    (many AcOk : (erased (List (Tk)) Z Y) (erased (List (Bool)) r u2 zr x3)
       (many (List (Rn)) R5) (erased (List (Bool)) r5 u5 yr) (erased (Den R5 r5) d5) (erased (Tb (Tt1) r5 u5) tb5)
       (erased (Xb Y u5 yr) yb) (erased (List (Bool)) x4) (erased (Rp (BTrue) n3 x3 x4) p)
       (erased (Nat) t) (erased (Run l3 (MkConf 2 (bits "00" x3) (BTrue) (bits "0" zr)) t (MkConf 2 (bits "00" x4) (BTrue) (bits "0" yr))) run)
       -> (AcR Z Y r u2 zr x3))
    (many AcNo : (erased (List (Tk)) Z Y) (erased (List (Bool)) r u2 zr x3) -> (AcR Z Y r u2 zr x3))))

(def-fns _ $ (many ct-run : (many (List (Rn)) R3) (erased (List (Tk)) W Y) (erased (List (Bool)) r u2 zr x3) (erased (Den R3 r) d3)
    (erased (Tb (Tt1) r u2) tb2) (erased (Xb (Cons (Tk) (Tp) (Cons (Tk) (T1) W)) u2 zr) zb) (erased (Cx W Y) cx)
    -> (many (AcR (Cons (Tk) (Tp) (Cons (Tk) (T1) W)) Y r u2 zr x3) res))
  (let ((erased Z)) (Cons (Tk) (Tp) (Cons (Tk) (T1) W)))
  (let ((many no)) (AcNo Z Y r u2 zr x3))
  (let-match erased tb2 (Tb1 _))
  (let-match many (strip (bits "00111111" (Nil (Bool))) R3 r d3) (StOk _ _ y1 R4 d4 cy) ((StNo _ _) no))
  (let-match erased (cat8 y1 r cy) (Refl _ _))
  (let-match many (strip (bits "0000" (Nil (Bool))) R4 y1 d4) (StOk _ _ r5 R5 d5 c4) ((StNo _ _) no))
  (let-match erased (cat4 r5 y1 c4) (Refl _ _))
  (let-match erased cx (MkCx _ _ s0 K1 sw wk))
  (let ((erased K0)) (Cons _ (Succ (Succ (Succ (Zero)))) (Cons _ (Succ s0) K1)))
  (let ((erased l)) (bits "00111" x3))
  (let ((erased e1) (erased cf1) (erased g1)) (gadget x3 u2 zr W zb))
  (let ((erased e2) (erased so) (erased g2)) (sw-ok _ W _ sw l u2 e1 cf1))
  (let-match erased so (SoE _ _ _ _ cf2))
  (let-match erased cf2 (CfB _ _ x2 _ _ _ ls2 xb2))
  (let-match erased xb2 (XbN _))
  (let ((erased x5) (erased ls3) (erased g3))
    (merge (Tt1) (Pl1) s0 K1 l x2 (bits "1111110000" r5) u2 (bits "11111110000" r5) ls2 (Tb1 _) (Tb1 _)))
  (let ((erased u3)) (bits "10000" r5))
  (let ((erased e3)) (MkTc 1 (DR) x5 (bits "11111110000" r5)))
  (let ((erased cf3)) (CfB l u3 x5 _ K0 (Cons _ (T0) $ Cons _ (T0) $ Nil (Tk)) ls3 (XbZ _ _ _ (XbZ _ _ _ (XbN u3)))))
  (let ((erased K3)) (Cons (Nat) n2 (Cons (Nat) n2 K0)))
  (let ((erased e4) (erased so4) (erased g4b))
    (sw-ok K0 (Cons _ (T0) $ Cons _ (T0) $ Nil (Tk)) (SEnd K3) (SwT0 K0 _ _ (SwT0 _ _ _ (SwEnd K3))) l u3 e3 cf3))
  (let-match erased so4 (SoE _ _ _ _ cf4))
  (let-match erased cf4 (CfB _ _ x4 _ _ _ ls4 xb4))
  (let-match erased xb4 (XbN _))
  (let ((erased u5) (erased tb5) (erased e5) (erased cf5) (erased po5) (erased g5))
    (en-ok K3 _ (Tt1) (Tt1) _ _ (EnMP (Tt1) (Pl1) n2 K0) l x4 r5 (bits "0000" r5) u3 ls4
      (RpS _ n3 r5 _ (RpS _ n2 r5 _ (rp2 _ r5))) (Tb1 _)))
  (let ((erased yr) (erased yb) (erased g6)) (wk-ok _ _ Y wk l u5 e5 cf5 po5))
  (let ((erased t) (erased run))
    (go-run 2 2 _ _ _ _ _ _ (go-cat _ _ _ g1 $ go-cat _ _ _ g2 $ go-cat _ _ _ g3 $ go-cat _ _ _ g4b $ go-cat _ _ _ g5 g6)))
  (AcOk Z Y r u2 zr x3 R5 r5 u5 yr d5 tb5 yb _ (rp3 _ x3) t run))

(def-adts
  ((Pa : ((List (Nat)) H D A) -> Type)
    enum
    (many PaE : (erased (List (Nat)) D) -> (Pa (Nil (Nat)) D (Cons (Nat) n2 D)))
    (many PaO : (erased (Nat) h) (erased (List (Nat)) D) -> (Pa (Cons (Nat) h (Nil (Nat))) D (Cons (Nat) n2 (Cons (Nat) h D))))))

(def-adts
  ((Pb : ((Fam) F) ((Nat) s) -> Type)
    enum
    (many PbOk : (erased (Fam) F) (erased (Nat) s) (many (List (Nat)) H) (many (List (Ps)) wf w) (erased (List (Nat)) D A) (erased (List (Tk)) X)
       (erased (Dg w (Cons (Nat) (Zero) (Nil (Nat))) D) g) (erased (Pa H D A) pa) (erased (DEnc A X) en) (erased (Phi F s X (Tt1)) ph) -> (Pb F s))
    (many PbNo : (erased (Fam) F) (erased (Nat) s) -> (Pb F s))))

(def-fns _ $ (many phi-pb : (many (Fam) F) (many (Nat) s) -> (many (Pb F s) r))
  (let ((many no)) (PbNo F s))
  (let ((many n) (erased mx)) (maxs-run F))
  (let-match many (lt-dec s (Succ n)) (Yes _ _ _ _ bn) ((No _ _ _ _ _) no))
  (let-match many F (FO P T)
    (else
      (let-match many (fam-e F) (FeOk _ P T ef) ((FeNo _) no))
      (let-match erased ef (Refl _ _))
      (let-match many T (Tt1) (else no))
      (let-match erased mx (MxE _ _ _ q))
      (let ((many t) (erased tq)) (top-run P))
      (let-match erased (top-fn P n t q tq) (Refl _ _))
      (let ((many w) (erased b)) (blk-fast P s t tq bn))
      (let ((erased D) (erased g)) (dg-tr w (Cons (Nat) (Zero) (Nil (Nat)))))
      (let ((erased X) (erased e)) (enc-tr (Cons (Nat) n2 D)))
      (PbOk F s (Nil (Nat)) w w D _ X g (PaE D) e (PhE P s (Tt1) w D X b g e))))
  (let-match many T (Tt1) (else no))
  (let ((many x) (many h) (many w) (erased D) (erased X) (erased g) (erased e) (erased ph)) (phi-blk P s (Tt1) n mx bn))
  (PbOk F s (Cons (Nat) h (Nil (Nat))) (Cons (Ps) x w) w D _ X g (PaO h D) e ph))

(def-fns _ $ (many pb-cells : (many (List (Nat)) H) (many (List (Ps)) w) (erased (List (Nat)) D A) (erased (List (Tk)) X)
    (erased (Dg w (Cons (Nat) (Zero) (Nil (Nat))) D) g) (erased (Pa H D A) pa) (erased (DEnc A X) en) -> (many (Nat) c) (erased (Rl X (Zero) c) r))
  (let ((many n) (erased dn)) (ds-dg w _ D g (Succ (Succ (Succ (Zero)))) (DsC (Zero) (Zero) (Zero) (Nil (Nat)) (DsN) (AddZero (Zero)))))
  (match many H _
    ((Nil _)
      (let-match erased pa (PaE _))
      (let ((many b) (erased ab)) (add (Succ (Succ (Zero))) n))
      (values (Succ (Succ (Succ b))) (enc-rl A X _ en (DsC n2 n b D dn ab))))
    ((Cons _ h _)
      (let-match erased pa (PaO _ _))
      (let ((many a) (erased aa)) (add h n))
      (let ((many b) (erased ab)) (add (Succ (Succ (Zero))) (Succ (Succ (Succ a)))))
      (values (Succ (Succ (Succ b))) (enc-rl A X _ en (DsC n2 _ b _ (DsC h n a D dn aa) ab))))))

(def-fns _ $ (erased ex3-pa : (erased (List (Nat)) H D D2 A A2) (erased (Pa H D A) pa) (erased (Pa H D2 A2) pa2) (erased (Ex3 D D2) x) -> (erased (Ex3 A A2) y))
  (match erased pa _
    ((PaE _) (let-match erased pa2 (PaE _)) (E3C n2 D D2 x))
    ((PaO h _) (let-match erased pa2 (PaO _ _)) (E3C n2 _ _ (E3C h D D2 x)))))

(def-adts
  ((Shp : ((List (Tk)) X) -> Type)
    enum
    (many MkShp : (erased (List (Tk)) W) (erased (E1 W) e) -> (Shp (Cons (Tk) (Tp) (Cons (Tk) (T1) W))))))

(def-fns _ $ (erased shp-of : (erased (List (Nat)) A1) (erased (List (Tk)) X) (erased (DEnc (Cons (Nat) n2 A1) X) en) (erased (D0 A1) d) -> (erased (Shp X) sh))
  (let-match erased en (EnC _ _ X1 _ e1 t))
  (let-match erased t (DtS k _ _ p))
  (let-match erased p (TpS _ _ _ p1))
  (let-match erased p1 (TpZ _))
  (MkShp X1 (enc-e1 A1 X1 e1 d)))

(def-fns _ $ (erased pb-shape : (erased (List (Ps)) w) (erased (List (Nat)) H D A) (erased (List (Tk)) X)
    (erased (Dg w (Cons (Nat) (Zero) (Nil (Nat))) D) g) (erased (Pa H D A) pa) (erased (DEnc A X) en) -> (erased (Shp X) sh))
  (let ((erased d0)) (dg-d0 w _ D g (D0O)))
  (match erased pa _
    ((PaE _) (shp-of D X en d0))
    ((PaO h _) (shp-of _ X en (d0-cons h D d0)))))
