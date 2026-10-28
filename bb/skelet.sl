(def-adts $ (Tl : -> Type)
  enum
  (many TV : -> (Tl))
  (many TZ : -> (Tl)))

(def-adts $ (Sd : -> Type)
  enum
  (many MkSd : (many (List (Bool)) seg) (many (Tl) f) -> (Sd)))

(def-adts $ (Tc : -> Type)
  enum
  (many MkTc : (many (Nat) q) (many (Mv) d) (many (List (Bool)) l r) -> (Tc)))

(def-adts $ (Ta : -> Type)
  enum
  (many MkTa : (many (Nat) q) (many (Mv) d) (many (Sd) l r) -> (Ta)))

(def-adts
  ((GS : ((Sd) s) ((List (Bool)) t) ((List (Bool)) xs) -> Type)
    enum
    (many GSV : (erased (List (Bool)) t) -> (GS (MkSd (Nil (Bool)) (TV)) t t))
    (many GSZ : (erased (List (Bool)) t) -> (GS (MkSd (Nil (Bool)) (TZ)) t (Nil (Bool))))
    (many GSC : (erased (List (Bool)) seg t xs) (erased (Tl) f) (erased (Bool) b) (erased (GS (MkSd seg f) t xs) g)
       -> (GS (MkSd (Cons (Bool) b seg) f) t (Cons (Bool) b xs)))))

(def-adts
  ((GT : ((Ta) a) ((List (Bool)) lt) ((List (Bool)) rt) ((Tc) e) -> Type)
    enum
    (many MkGT : (erased (Nat) q) (erased (Mv) d) (erased (Sd) L R) (erased (List (Bool)) lt rt l r)
       (erased (GS L lt l) gl) (erased (GS R rt r) gr) -> (GT (MkTa q d L R) lt rt (MkTc q d l r)))))

(def-adts
  ((AsC : ((Tc) e) ((Conf) c) -> Type)
    enum
    (many MkAsC : (erased (Nat) q) (erased (Mv) d) (erased (List (Bool)) l r x y x1 l1 r1) (erased (Bool) h)
       (erased (Ori (List (Bool)) d l r x y) o) (erased (Pull x h x1) pp) (erased (Ori (List (Bool)) d l1 r1 x1 y) o2)
       -> (AsC (MkTc q d l r) (MkConf q l1 h r1)))))

(def-adts
  ((SPop : ((Sd) s) ((Bool) b) ((Sd) s2) -> Type)
    enum
    (many SPC : (erased (List (Bool)) seg) (erased (Tl) f) (erased (Bool) b) -> (SPop (MkSd (Cons (Bool) b seg) f) b (MkSd seg f)))
    (many SPZ : -> (SPop (MkSd (Nil (Bool)) (TZ)) (BFalse) (MkSd (Nil (Bool)) (TZ))))))

(def-adts
  ((TStep : ((List (PT)) p) ((Tc) e) ((Tc) e2) -> Type)
    enum
    (many MkTS : (erased (List (PT)) p) (erased (Nat) q q2) (erased (Mv) d e) (erased (Bool) w h) (erased (List (Bool)) l r l1 r1 u v l2 r2)
       (erased (AsC (MkTc q d l r) (MkConf q l1 h r1)) ac) (erased (PLook p q h (Def (Mov w e q2))) pl)
       (erased (Ori (List (Bool)) e l1 r1 u v) o) (erased (Ori (List (Bool)) e l2 r2 u (Cons (Bool) w v)) o2)
       -> (TStep p (MkTc q d l r) (MkTc q2 e l2 r2)))))

(def-adts
  ((AStep : ((List (PT)) p) ((Ta) a) ((Ta) a2) -> Type)
    enum
    (many MkAS : (erased (List (PT)) p) (erased (Nat) q q2) (erased (Mv) d e) (erased (Bool) w h) (erased (Sd) L R X Y X1 L1 R1 U L2 R2)
       (erased (List (Bool)) seg) (erased (Tl) f)
       (erased (Ori (Sd) d L R X Y) o) (erased (SPop X h X1) sp) (erased (Ori (Sd) d L1 R1 X1 Y) o2)
       (erased (PLook p q h (Def (Mov w e q2))) pl)
       (erased (Ori (Sd) e L1 R1 U (MkSd seg f)) o3) (erased (Ori (Sd) e L2 R2 U (MkSd (Cons (Bool) w seg) f)) o4)
       -> (AStep p (MkTa q d L R) (MkTa q2 e L2 R2)))))

(def-adts
  ((ARun : ((List (PT)) p) ((Ta) a) ((Ta) a2) -> Type)
    enum
    (many AR1 : (erased (List (PT)) p) (erased (Ta) a a2) (erased (AStep p a a2) st) -> (ARun p a a2))
    (many ARS : (erased (List (PT)) p) (erased (Ta) a a1 a2) (erased (AStep p a a1) st) (erased (ARun p a1 a2) r) -> (ARun p a a2))))

(def-adts
  ((XRun : ((List (PT)) p) ((Conf) c) ((Conf) d) ((Bool) g) -> Type)
    enum
    (many XR0 : (erased (List (PT)) p) (erased (Conf) c) -> (XRun p c c (BFalse)))
    (many XRS : (erased (List (PT)) p) (erased (Conf) c c1 d) (erased (Bool) g) (erased (PStep p c c1) st) (erased (XRun p c1 d g) r)
       -> (XRun p c d (BTrue)))))

(def-adts
  ((Reach : ((List (PT)) p) ((Tc) e) ((Tc) e2) ((Bool) g) -> Type)
    enum
    (many MkRc : (erased (List (PT)) p) (erased (Tc) e e2) (erased (Bool) g) (erased (Conf) c c2)
       (erased (AsC e c) a) (erased (AsC e2 c2) a2) (erased (XRun p c c2 g) r) -> (Reach p e e2 g))))

(def-adts
  ((Orb : ((Bool) a) ((Bool) b) ((Bool) c) -> Type)
    enum
    (many OrbT : (erased (Bool) b) -> (Orb (BTrue) b (BTrue)))
    (many OrbF : (erased (Bool) b) -> (Orb (BFalse) b b))))

(def-fns _ $ (erased ori-xy : (erased Type A) (erased (Mv) d) (erased A l r x y x2 y2) (erased (Ori A d l r x y) o) (erased (Ori A d l r x2 y2) o2)
    -> (erased (Eq A x x2) e1) (erased (Eq A y y2) e2))
  (match erased o _
    ((OrL _ _ _) (let-match erased o2 (OrL _ _ _)) (values (Refl A x) (Refl A y)))
    ((OrR _ _ _) (let-match erased o2 (OrR _ _ _)) (values (Refl A x) (Refl A y)))))

(def-fns _ $ (erased ori-lr : (erased Type A) (erased (Mv) d) (erased A l r l2 r2 x y) (erased (Ori A d l r x y) o) (erased (Ori A d l2 r2 x y) o2)
    -> (erased (Eq A l l2) e1) (erased (Eq A r r2) e2))
  (match erased o _
    ((OrL _ _ _) (let-match erased o2 (OrL _ _ _)) (values (Refl A l) (Refl A r)))
    ((OrR _ _ _) (let-match erased o2 (OrR _ _ _)) (values (Refl A l) (Refl A r)))))

(def-fns _ $ (erased ori-gs : (erased (Mv) d) (erased (Sd) L R X Y) (erased (List (Bool)) lt rt l r) (erased (Ori (Sd) d L R X Y) o)
    (erased (GS L lt l) gl) (erased (GS R rt r) gr) ->
    (erased (List (Bool)) x y tx ty) (erased (Ori (List (Bool)) d l r x y) oc) (erased (Ori (List (Bool)) d lt rt tx ty) ot)
    (erased (GS X tx x) gx) (erased (GS Y ty y) gy))
  (match erased o _
    ((OrL _ _ _) (values l r lt rt (OrL _ l r) (OrL _ lt rt) gl gr))
    ((OrR _ _ _) (values r l rt lt (OrR _ l r) (OrR _ lt rt) gr gl))))

(def-fns _ $ (erased gs-ori : (erased (Mv) d) (erased (Sd) L R X Y) (erased (List (Bool)) lt rt tx ty x y) (erased (Ori (Sd) d L R X Y) o)
    (erased (Ori (List (Bool)) d lt rt tx ty) ot) (erased (GS X tx x) gx) (erased (GS Y ty y) gy) ->
    (erased (List (Bool)) l r) (erased (Ori (List (Bool)) d l r x y) oc) (erased (GS L lt l) gl) (erased (GS R rt r) gr))
  (match erased o _
    ((OrL _ _ _) (let-match erased ot (OrL _ _ _)) (values x y (OrL _ x y) gx gy))
    ((OrR _ _ _) (let-match erased ot (OrR _ _ _)) (values y x (OrR _ y x) gy gx))))

(def-fns _ $ (erased spop-ok : (erased (Sd) X X1) (erased (Bool) h) (erased (List (Bool)) t x) (erased (SPop X h X1) sp) (erased (GS X t x) g)
    -> (erased (List (Bool)) x1) (erased (Pull x h x1) pp) (erased (GS X1 t x1) g1))
  (match erased sp _
    ((SPC seg f b) (let-match erased g (GSC _ _ x1 _ _ g1)) (values x1 (PullCons h x1) g1))
    ((SPZ) (let-match erased g (GSZ _)) (values (Nil (Bool)) (PullNil) (GSZ t)))))

(def-fns _ $ (erased as-ex : (erased (Tc) e) -> (erased (Conf) c) (erased (AsC e c) a))
  (let-match erased e (MkTc q d l r))
  (let ((erased x) (erased y) (erased o)) (ori-of _ d l r))
  (let ((erased h) (erased x1) (erased pp)) (pop x))
  (let ((erased l1) (erased r1) (erased o2)) (ori-mk _ d x1 y))
  (values (MkConf q l1 h r1) (MkAsC q d l r x y x1 l1 r1 h o pp o2)))

(def-fns _ $ (erased as-fn : (erased (Tc) e) (erased (Conf) c c2) (erased (AsC e c) a) (erased (AsC e c2) a2) -> (erased (Eq (Conf) c c2) eq))
  (let-match erased a (MkAsC q d l r x y x1 l1 r1 h o pp o2))
  (let-match erased a2 (MkAsC _ _ _ _ x' y' x1' l1' r1' h' o' pp' o2'))
  (let ((erased ex) (erased ey)) (ori-xy _ d l r x y x' y' o o'))
  (let-match erased ex (Refl _ _))
  (let-match erased ey (Refl _ _))
  (let ((erased eh) (erased ex1)) (pop-fn x x1 x1' h h' pp pp'))
  (let-match erased eh (Refl _ _))
  (let-match erased ex1 (Refl _ _))
  (let ((erased el) (erased er)) (ori-lr _ d l1 r1 l1' r1' x1 y o2 o2'))
  (let-match erased el (Refl _ _))
  (let-match erased er (Refl _ _))
  (Refl (Conf) c))

(def-fns _ $ (erased tstep-ok : (erased (List (PT)) p) (erased (Tc) e e2) (erased (Conf) c) (erased (TStep p e e2) ts) (erased (AsC e c) a)
    -> (erased (Conf) c2) (erased (AsC e2 c2) a2) (erased (PStep p c c2) st))
  (let-match erased ts (MkTS _ q q2 d e1 w h l r l1 r1 u v l2 r2 a0 pl o o2))
  (let-match erased (as-fn e c (MkConf q l1 h r1) a a0) (Refl _ _))
  (let ((erased h2) (erased ua) (erased pp)) (pop u))
  (match erased o _
    ((OrL _ _ _)
      (let-match erased o2 (OrL _ _ _))
      (values (MkConf q2 ua h2 (Cons (Bool) w r1)) (MkAsC q2 e1 l1 (Cons (Bool) w r1) l1 (Cons (Bool) w r1) ua ua (Cons (Bool) w r1) h2 (OrL _ _ _) pp (OrL _ _ _))
        (PStepL p q q2 l1 r1 ua h w h2 pl pp)))
    ((OrR _ _ _)
      (let-match erased o2 (OrR _ _ _))
      (values (MkConf q2 (Cons (Bool) w l1) h2 ua) (MkAsC q2 e1 (Cons (Bool) w l1) r1 r1 (Cons (Bool) w l1) ua (Cons (Bool) w l1) ua h2 (OrR _ _ _) pp (OrR _ _ _))
        (PStepR p q q2 l1 r1 ua h w h2 pl pp)))))

(def-fns _ $ (erased astep-ok : (erased (List (PT)) p) (erased (Ta) a a2) (erased (List (Bool)) lt rt) (erased (Tc) e) (erased (AStep p a a2) st) (erased (GT a lt rt e) g)
    -> (erased (Tc) e2) (erased (TStep p e e2) ts) (erased (GT a2 lt rt e2) g2))
  (let-match erased st (MkAS _ q q2 d e1 w h L R X Y X1 L1 R1 U L2 R2 seg f o sp o2 pl o3 o4))
  (let-match erased g (MkGT _ _ _ _ _ _ l r gl gr))
  (let ((erased x) (erased y) (erased tx) (erased ty) (erased oc) (erased ot) (erased gx) (erased gy)) (ori-gs d L R X Y lt rt l r o gl gr))
  (let ((erased x1) (erased pp) (erased gx1)) (spop-ok X X1 h tx x sp gx))
  (let ((erased l1) (erased r1) (erased oc2) (erased gl1) (erased gr1)) (gs-ori d L1 R1 X1 Y lt rt tx ty x1 y o2 ot gx1 gy))
  (let ((erased u) (erased v) (erased tu) (erased tv) (erased oc3) (erased ot3) (erased gu) (erased gv)) (ori-gs e1 L1 R1 U (MkSd seg f) lt rt l1 r1 o3 gl1 gr1))
  (let ((erased l2) (erased r2) (erased oc4) (erased gl2) (erased gr2))
    (gs-ori e1 L2 R2 U (MkSd (Cons (Bool) w seg) f) lt rt tu tv u (Cons (Bool) w v) o4 ot3 gu (GSC seg tv v f w gv)))
  (values (MkTc q2 e1 l2 r2) (MkTS p q q2 d e1 w h l r l1 r1 u v l2 r2 (MkAsC q d l r x y x1 l1 r1 h oc pp oc2) pl oc3 oc4)
    (MkGT q2 e1 L2 R2 lt rt l2 r2 gl2 gr2)))

(def-fns _ $ (erased arun-ok : (erased (List (PT)) p) (erased (Ta) a a2) (erased (List (Bool)) lt rt) (erased (Tc) e) (erased (Conf) c)
    (subterm erased (ARun p a a2) ar) (erased (GT a lt rt e) g) (erased (AsC e c) ac)
    -> (erased (Tc) e2) (erased (Conf) c2) (erased (GT a2 lt rt e2) g2) (erased (AsC e2 c2) ac2) (erased (XRun p c c2 (BTrue)) xr))
  (match erased ar _
    ((AR1 _ _ _ st)
      (let ((erased e1) (erased ts) (erased g1)) (astep-ok p a a2 lt rt e st g))
      (let ((erased c1) (erased ac1) (erased ps)) (tstep-ok p e e1 c ts ac))
      (values e1 c1 g1 ac1 (XRS p c c1 c1 (BFalse) ps (XR0 p c1))))
    ((ARS _ _ a1 _ st ar1)
      (let ((erased e1) (erased ts) (erased g1)) (astep-ok p a a1 lt rt e st g))
      (let ((erased c1) (erased ac1) (erased ps)) (tstep-ok p e e1 c ts ac))
      (let ((erased e2) (erased c2) (erased g2) (erased ac2) (erased xr)) (arun-ok p a1 a2 lt rt e1 c1 ar1 g1 ac1))
      (values e2 c2 g2 ac2 (XRS p c c1 c2 (BTrue) ps xr)))))

(def-fns _ $ (erased gs-fn : (erased (Sd) s) (erased (List (Bool)) t x x2) (subterm erased (GS s t x) g) (erased (GS s t x2) g2) -> (erased (Eq (List (Bool)) x x2) e))
  (match erased g _
    ((GSV _) (let-match erased g2 (GSV _)) (Refl _ x))
    ((GSZ _) (let-match erased g2 (GSZ _)) (Refl _ x))
    ((GSC seg _ x1 f b g1)
      (let-match erased g2 (GSC _ _ x3 _ _ g3))
      (let-match erased (gs-fn (MkSd seg f) t x1 x3 g1 g3) (Refl _ _))
      (Refl _ x))))

(def-fns _ $ (erased arun-reach : (erased (List (PT)) p) (erased (Ta) a a2) (erased (List (Bool)) lt rt) (erased (Tc) e e2)
    (erased (ARun p a a2) ar) (erased (GT a lt rt e) g) (erased (GT a2 lt rt e2) g2) -> (erased (Reach p e e2 (BTrue)) rc))
  (let ((erased c) (erased ac)) (as-ex e))
  (let ((erased e3) (erased c2) (erased g3) (erased ac2) (erased xr)) (arun-ok p a a2 lt rt e c ar g ac))
  (let-match erased g2 (MkGT q d L R _ _ l r gl gr))
  (let-match erased g3 (MkGT _ _ _ _ _ _ l3 r3 gl3 gr3))
  (let-match erased (gs-fn L lt l l3 gl gl3) (Refl _ _))
  (let-match erased (gs-fn R rt r r3 gr gr3) (Refl _ _))
  (MkRc p e e2 (BTrue) c c2 ac ac2 xr))

(def-fns _ $ (erased xrun-cat : (erased (List (PT)) p) (erased (Conf) c d e) (erased (Bool) g1 g2) (subterm erased (XRun p c d g1) r1) (erased (XRun p d e g2) r2)
    -> (erased (Bool) g) (erased (Orb g1 g2 g) o) (erased (XRun p c e g) r))
  (let-match erased r1 (XRS _ _ c1 _ g st r3) ((XR0 _ _) (values g2 (OrbF g2) r2)))
  (let ((erased g3) (erased o) (erased r4)) (xrun-cat p c1 d e g g2 r3 r2))
  (values (BTrue) (OrbT g2) (XRS p c c1 e g3 st r4)))

(def-fns _ $ (erased reach-cat : (erased (List (PT)) p) (erased (Tc) e1 e2 e3) (erased (Bool) g1 g2) (erased (Reach p e1 e2 g1) ra) (erased (Reach p e2 e3 g2) rb)
    -> (erased (Bool) g) (erased (Orb g1 g2 g) o) (erased (Reach p e1 e3 g) r))
  (let-match erased ra (MkRc _ _ _ _ c1 c2 a1 a2 x1))
  (let-match erased rb (MkRc _ _ _ _ c3 c4 a3 a4 x2))
  (let-match erased (as-fn e2 c2 c3 a2 a3) (Refl _ _))
  (let ((erased g) (erased o) (erased x)) (xrun-cat p c1 c2 c4 g1 g2 x1 x2))
  (values g o (MkRc p e1 e3 g c1 c4 a1 a4 x)))

(def-fns _ $ (erased reach-catT : (erased (List (PT)) p) (erased (Tc) e1 e2 e3) (erased (Bool) g2) (erased (Reach p e1 e2 (BTrue)) ra) (erased (Reach p e2 e3 g2) rb)
    -> (erased (Reach p e1 e3 (BTrue)) r))
  (let ((erased g) (erased o) (erased r)) (reach-cat p e1 e2 e3 (BTrue) g2 ra rb))
  (let-match erased o (OrbT _))
  r)

(def-fns _ $ (erased reach-refl : (erased (List (PT)) p) (erased (Tc) e) -> (erased (Reach p e e (BFalse)) r))
  (let ((erased c) (erased a)) (as-ex e))
  (MkRc p e e (BFalse) c c a a (XR0 p c)))

(def-fns _ $ (erased reach-cat2 : (erased (List (PT)) p) (erased (Tc) e1 e2 e3) (erased (Bool) g1) (erased (Reach p e1 e2 g1) ra) (erased (Reach p e2 e3 (BTrue)) rb)
    -> (erased (Reach p e1 e3 (BTrue)) r))
  (let ((erased g) (erased o) (erased r)) (reach-cat p e1 e2 e3 g1 (BTrue) ra rb))
  (let-match erased o (OrbT _) ((OrbF _) r))
  r)

(def-fns _ $ (erased pstep-stp : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Conf) c d) (erased (PStep p c d) st)
    -> (erased (Stp m c d) st2))
  (match erased st _
    ((PStepL _ q q2 l r l2 h w h2 pl pp) (StepL m q q2 l r l2 h w h2 (ext-look p m q h _ ex pl) pp))
    ((PStepR _ q q2 l r r2 h w h2 pl pp) (StepR m q q2 l r r2 h w h2 (ext-look p m q h _ ex pl) pp))))

(def-fns _ $ (erased xrun-halts : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Conf) c d) (erased (Bool) g) (erased (Nat) u)
    (subterm erased (XRun p c d g) xr) (erased (HaltsAt m c u) hs) -> (erased (Nat) v) (erased (HaltsAt m d v) hd) (erased (Lt v (Succ u)) lt))
  (let-match erased xr (XRS _ _ c1 _ g1 st xr1) ((XR0 _ _) (values u hs (lt-succ u))))
  (let ((erased s1)) (pstep-stp p m ex c c1 st))
  (let-match erased hs (HMove _ _ d2 ua st2 hs2) (absurd (HStop _ q l r h lk) (no-step m q l r h c1 lk s1)))
  (let-match erased (step-fn m c c1 d2 s1 st2) (Refl _ _))
  (let ((erased v) (erased hd) (erased lt)) (xrun-halts p m ex c1 d g1 ua xr1 hs2))
  (values v hd (lt-weaken v u lt)))

(def-fns _ $ (erased reach-halts : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Tc) e e2) (erased (Conf) c) (erased (Nat) u)
    (erased (Reach p e e2 (BTrue)) rc) (erased (AsC e c) ac) (erased (HaltsAt m c u) hs)
    -> (erased (Conf) c2) (erased (AsC e2 c2) ac2) (erased (Nat) v) (erased (HaltsAt m c2 v) hd) (erased (Lt v u) lt))
  (let-match erased rc (MkRc _ _ _ _ c1 c2 a1 a2 xr))
  (let-match erased (as-fn e c c1 ac a1) (Refl _ _))
  (let-match erased xr (XRS _ _ c3 _ g1 st xr1))
  (let ((erased s1)) (pstep-stp p m ex c c3 st))
  (let-match erased hs (HMove _ _ d2 ua st2 hs2) (absurd (HStop _ q l r h lk) (no-step m q l r h c3 lk s1)))
  (let-match erased (step-fn m c c3 d2 s1 st2) (Refl _ _))
  (let ((erased v) (erased hd) (erased lt)) (xrun-halts p m ex c3 c2 g1 ua xr1 hs2))
  (values c2 a2 v hd lt))

(def-adts
  ((SPopR : ((Sd) s) -> Type)
    enum
    (many SPOk : (erased (Sd) s) (many (Bool) b) (many (List (Bool)) seg) (many (Tl) f) (erased (SPop s b (MkSd seg f)) sp) -> (SPopR s))
    (many SPNo : (erased (Sd) s) -> (SPopR s))))

(def-fns _ $ (many spop : (many (Sd) s) -> (many (SPopR s) r))
  (let-match many s (MkSd seg f))
  (let-match many seg (Cons _ b seg1) ((Nil _) (match many f _ ((TZ) (SPOk s (BFalse) seg f (SPZ))) ((TV) (SPNo s)))))
  (SPOk s b seg1 f (SPC seg1 f b)))

(def-adts
  ((AStepR : ((List (PT)) p) ((Ta) a) -> Type)
    enum
    (many ASOk : (erased (List (PT)) p) (erased (Ta) a) (many (Ta) a2) (erased (AStep p a a2) st) -> (AStepR p a))
    (many ASNo : (erased (List (PT)) p) (erased (Ta) a) -> (AStepR p a))))

(def-fns _ $ (many astep : (many (List (PT)) p) (many (Ta) a) -> (many (AStepR p a) r))
  (let-match many a (MkTa q d L R))
  (let ((many X) (many Y) (erased o)) (ori-of _ d L R))
  (let-match many (spop X) (SPOk _ h seg1 f1 sp) ((SPNo _) (ASNo p a)))
  (let ((many L1) (many R1) (erased o2)) (ori-mk _ d (MkSd seg1 f1) Y))
  (let-match many (plook p q h) (PLOk _ _ _ x pl) ((PLNo _ _ _) (ASNo p a)))
  (let-match many x (Def t) ((Undef) (ASNo p a)))
  (let-match many t (Mov w e q2) ((Hlt) (ASNo p a)))
  (let ((many U) (many V) (erased o3)) (ori-of _ e L1 R1))
  (let-match many V (MkSd seg f))
  (let ((many L2) (many R2) (erased o4)) (ori-mk _ e U (MkSd (Cons (Bool) w seg) f)))
  (ASOk p a (MkTa q2 e L2 R2) (MkAS p q q2 d e w h L R X Y (MkSd seg1 f1) L1 R1 U L2 R2 seg f o sp o2 pl o3 o4)))

(def-fns _ $ (many eq-tl : (many (Tl) a) (many (Tl) b) -> (many (Maybe (Eq (Tl) a b)) r))
  (match many a _
    ((TV) (match many b _ ((TV) (Some _ (Refl (Tl) a))) ((TZ) (None _))))
    ((TZ) (match many b _ ((TZ) (Some _ (Refl (Tl) a))) ((TV) (None _))))))

(def-fns _ $ (many eq-sd : (many (Sd) a) (many (Sd) b) -> (many (Maybe (Eq (Sd) a b)) r))
  (let-match many a (MkSd s f))
  (let-match many b (MkSd s2 f2))
  (let-match many (eq-bl s s2) (Some _ e1) ((None _) (None _)))
  (let-match erased e1 (Refl _ _))
  (let-match many (eq-tl f f2) (Some _ e2) ((None _) (None _)))
  (let-match erased e2 (Refl _ _))
  (Some _ (Refl (Sd) a)))

(def-fns _ $ (many eq-ta : (many (Ta) a) (many (Ta) b) -> (many (Maybe (Eq (Ta) a b)) r))
  (let-match many a (MkTa q d L R))
  (let-match many b (MkTa q2 d2 L2 R2))
  (let-match many (eq-nat q q2) (Some _ e1) ((None _) (None _)))
  (let-match erased e1 (Refl _ _))
  (let-match many (eq-dir d d2) (Some _ e2) ((None _) (None _)))
  (let-match erased e2 (Refl _ _))
  (let-match many (eq-sd L L2) (Some _ e3) ((None _) (None _)))
  (let-match erased e3 (Refl _ _))
  (let-match many (eq-sd R R2) (Some _ e4) ((None _) (None _)))
  (let-match erased e4 (Refl _ _))
  (Some _ (Refl (Ta) a)))

(def-fns _ $ (many srun : (many (List (PT)) p) (many (Ta) a b) (subterm many (Nat) fuel) -> (many (Res (ARun p a b)) r))
  (let-match many fuel (Succ f) ((Zero) (RFail _)))
  (let-match many (astep p a) (ASOk _ _ a1 st) ((ASNo _ _) (RFail _)))
  (let-match many (eq-ta a1 b) (None _) ((Some _ e) (let-match erased e (Refl _ _)) (ROk _ (AR1 p a a1 st))))
  (let-match many (notail $ srun p a1 b f) (ROk _ ar) ((RFail _) (RFail _)))
  (ROk _ (ARS p a a1 b st ar)))

(def-fns _ $ (many raw1 : (many (Pos) here) (many (List $ Raw) rs) -> (many (Raw) r))
  (let-match many rs (Cons _ r _) ((Nil _) (RawWild here)))
  r)

(def-fns _ $ (many raw-app : (many (Pos) here) (many (Raw) f) (many (Raw) x) -> (many (Raw) r))
  (let-match many f (RawList p xs) (else (RawList here $ Cons _ f $ Cons _ x $ Nil _)))
  (RawList p (raws-append xs $ Cons _ x $ Nil _)))

(def-fns _ $ (many bits-raw : (many (Pos) here) (subterm many (String) s) (many (Raw) t c0 c1) -> (many (Raw) r))
  (let-match many s (SCons c rest) ((SNil) t))
  (let ((many x)) (notail $ bits-raw here rest t c0 c1))
  (raw-app here (match many (ch-is c #\1) (((Raw) f)) ((BTrue) c1) ((BFalse) c0)) x))

(def-macro (bits args here mw)
  (let ((many usage)) "`bits` takes a string of 0s and 1s and an optional tail")
  (let-match many args (Cons _ s r1) ((Nil _) (macro-fail mw here usage)))
  (let ((unique mw1) (many ms)) (arg-string mw s))
  (let-match many ms (Some _ str) ((None _) (macro-fail mw1 here usage)))
  (let ((many t)) (match many r1 (((Raw) t)) ((Cons _ t _) t) ((Nil _) (raw1 here (qq (Nil (Bool)))))))
  (values mw1 $ Cons _ (bits-raw here str t (raw1 here (qq (Cons (Bool) (BFalse)))) (raw1 here (qq (Cons (Bool) (BTrue))))) $ Nil _))

(def-adts $ (SkForms : -> Type)
  enum
  (many SkOk : (many (Raw) ta tc gt) -> (SkForms))
  (many SkBad : -> (SkForms)))

(def-fns _ $ (many sk-forms : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (Raw) spec lt rt) ->
    (unique (MacroWorld) mw2 at mw) (many (SkForms) r))
  (let-match many spec (RawList _ xs) (else (values mw (SkBad))))
  (let-match many xs (Cons _ q x1) ((Nil _) (values mw (SkBad))))
  (let-match many x1 (Cons _ d x2) ((Nil _) (values mw (SkBad))))
  (let-match many x2 (Cons _ l x3) ((Nil _) (values mw (SkBad))))
  (let-match many x3 (Cons _ lf x4) ((Nil _) (values mw (SkBad))))
  (let-match many x4 (Cons _ r x5) ((Nil _) (values mw (SkBad))))
  (let-match many x5 (Cons _ rf _) ((Nil _) (values mw (SkBad))))
  (let ((unique mw1) (many ml)) (arg-string mw l))
  (let-match many ml (Some _ sl) ((None _) (values mw1 (SkBad))))
  (let ((unique mw2) (many mr)) (arg-string mw1 r))
  (let-match many mr (Some _ sr) ((None _) (values mw2 (SkBad))))
  (let ((many nil)) (raw1 here (qq (Nil (Bool)))))
  (let ((many c0)) (raw1 here (qq (Cons (Bool) (BFalse)))))
  (let ((many c1)) (raw1 here (qq (Cons (Bool) (BTrue)))))
  (let ((many gc)) (raw1 here (qq (GSC _ _ _ _ _))))
  (let ((many tz)) (RawSymbol here (SName "TZ")))
  (let ((many gz)) (raw1 here (qq (GSZ _))))
  (let ((many gv)) (raw1 here (qq (GSV _))))
  (let ((many tl) (many el)) (match many (same-sym lf tz) (((Raw) a) ((Raw) b)) ((BTrue) (values nil gz)) ((BFalse) (values lt gv))))
  (let ((many tr) (many er)) (match many (same-sym rf tz) (((Raw) a) ((Raw) b)) ((BTrue) (values nil gz)) ((BFalse) (values rt gv))))
  (values mw2 (SkOk
    (raw1 here (qq (MkTa (~ q) ((~ d)) (MkSd (~ (bits-raw here sl nil c0 c1)) ((~ lf))) (MkSd (~ (bits-raw here sr nil c0 c1)) ((~ rf))))))
    (raw1 here (qq (MkTc (~ q) ((~ d)) (~ (bits-raw here sl tl c0 c1)) (~ (bits-raw here sr tr c0 c1)))))
    (raw1 here (qq (MkGT _ _ _ _ _ _ _ _ (~ (bits-raw here sl el gc gc)) (~ (bits-raw here sr er gc gc))))))))

(def-adts $ (SkE : -> Type)
  enum
  (many MkSkE : (many (Raw) name g ta tb tca tcb gta gtb) -> (SkE)))

(def-fns _ $ (many sk-ents : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (Raw) lt rt) (subterm many (List $ Raw) es) ->
    (unique (MacroWorld) mw2 at mw) (many (Maybe (List (SkE))) r))
  (let-match many es (Cons _ e rest) ((Nil _) (values mw (Some _ (Nil _)))))
  (let-match many e (RawList _ xs) (else (values mw (None _))))
  (let-match many xs (Cons _ name x1) ((Nil _) (values mw (None _))))
  (let-match many x1 (Cons _ sa x2) ((Nil _) (values mw (None _))))
  (let-match many x2 (Cons _ sb _) ((Nil _) (values mw (None _))))
  (let ((unique mw1) (many g)) (fresh-raw mw here "g"))
  (let ((unique mw2) (many fa)) (sk-forms mw1 here sa lt rt))
  (let-match many fa (SkOk ta tca gta) ((SkBad) (values mw2 (None _))))
  (let ((unique mw3) (many fb)) (sk-forms mw2 here sb lt rt))
  (let-match many fb (SkOk tb tcb gtb) ((SkBad) (values mw3 (None _))))
  (let ((unique mw4) (many r)) (notail $ sk-ents mw3 here lt rt rest))
  (let-match many r (Some _ ys) ((None _) (values mw4 (None _))))
  (values mw4 (Some _ (Cons _ (MkSkE name g ta tb tca tcb gta gtb) ys))))

(def-fns _ $ (many sk-parts : (many (Pos) here) (many (Raw) p) (subterm many (List (SkE)) es) -> (many (List $ Raw) fields checks gs))
  (let-match many es (Cons _ e rest) ((Nil _) (values (Nil _) (Nil _) (Nil _))))
  (let-match many e (MkSkE _ g ta tb _ _ _ _))
  (let ((many fs) (many cs) (many hs)) (notail $ sk-parts here p rest))
  (values (Cons _ (raw1 here (qq (erased (ARun (~ p) (~ ta) (~ tb)) (~ g)))) fs)
    (Cons _ (raw1 here (qq (let-match many (srun (~ p) (~ ta) (~ tb) 3000) (ROk _ (~ g)) ((RFail _) (RFail _))))) cs)
    (Cons _ g hs)))

(def-fns _ $ (many sk-lemmas : (many (Pos) here) (many (Raw) p fam ctor sg lt rt) (many (List $ Raw) gs) (subterm many (List (SkE)) es) -> (many (List $ Raw) r))
  (let-match many es (Cons _ e rest) ((Nil _) (Nil _)))
  (let-match many e (MkSkE name g _ _ tca tcb gta gtb))
  (raws-append
    (qq (def-fns _ $ (erased (~ name) : (erased (List (PT)) (~ p)) (erased ((~ fam) (~ p)) (~ sg)) (erased (List (Bool)) (~ lt) (~ rt))
        -> (erased (Reach (~ p) (~ tca) (~ tcb) (BTrue)) _))
      (let-match erased (~ sg) ((~ ctor) _ (~@ gs)))
      (arun-reach (~ p) _ _ (~ lt) (~ rt) _ _ (~ g) (~ gta) (~ gtb))))
    (notail $ sk-lemmas here p fam ctor sg lt rt gs rest)))

(def-macro (sk-family args here mw)
  (let ((many usage)) "`sk-family` takes a family name, its constructor, a checker name and `(lemma (q d left-bits left-tail right-bits right-tail) (...))` segments")
  (let-match many args (Cons _ fam r1) ((Nil _) (macro-fail mw here usage)))
  (let-match many r1 (Cons _ ctor r2) ((Nil _) (macro-fail mw here usage)))
  (let-match many r2 (Cons _ chk es) ((Nil _) (macro-fail mw here usage)))
  (let ((unique mw1) (many lt)) (fresh-raw mw here "lt"))
  (let ((unique mw2) (many rt)) (fresh-raw mw1 here "rt"))
  (let ((unique mw3) (many p)) (fresh-raw mw2 here "p"))
  (let ((unique mw4) (many sg)) (fresh-raw mw3 here "sg"))
  (let ((unique mw5) (many r)) (sk-ents mw4 here lt rt es))
  (let-match many r (Some _ xs) ((None _) (macro-fail mw5 here usage)))
  (let ((many fields) (many checks) (many gs)) (sk-parts here p xs))
  (values mw5 $ raws-append
    (qq (def-adts $ ((~ fam) : ((List (PT)) (~ p)) -> Type)
          enum
          (many (~ ctor) : (erased (List (PT)) (~ p)) (~@ fields) -> ((~ fam) (~ p))))
        (def-fns _ $ (many (~ chk) : (many (List (PT)) (~ p)) -> (many (Res ((~ fam) (~ p))) _))
          (~@ checks)
          (ROk _ ((~ ctor) (~ p) (~@ gs)))))
    (sk-lemmas here p fam ctor sg lt rt gs xs)))

(def-adts $ (Dorf : -> Type)
  enum
  (many ZE : -> (Dorf))
  (many ZO : (many (Dorf) n) -> (Dorf))
  (many ZI : (many (Dorf) n) -> (Dorf)))

(def-adts
  ((Zi : ((Dorf) n) ((Dorf) m) -> Type)
    enum
    (many ZiE : -> (Zi (ZE) (ZI (ZE))))
    (many ZiO : (erased (Dorf) n) -> (Zi (ZO n) (ZI n)))
    (many ZiI : (erased (Dorf) n m) (erased (Zi n m) z) -> (Zi (ZI n) (ZO (ZO m))))))

(def-adts
  ((Inc : ((Dorf) n) ((Dorf) m) -> Type)
    enum
    (many IncE : -> (Inc (ZE) (ZI (ZE))))
    (many IncO : (erased (Dorf) n m) (erased (Zi n m) z) -> (Inc (ZO n) m))
    (many IncI : (erased (Dorf) n m) (erased (Zi n m) z) -> (Inc (ZI n) (ZO m)))))

(def-adts
  ((ZR : ((Dorf) n) ((List (Bool)) x) -> Type)
    enum
    (many ZRE : -> (ZR (ZE) (Nil (Bool))))
    (many ZRO : (erased (Dorf) n) (erased (List (Bool)) x) (erased (ZR n x) z) -> (ZR (ZO n) (Cons (Bool) (BFalse) x)))
    (many ZRI : (erased (Dorf) n) (erased (List (Bool)) x) (erased (ZR n x) z) -> (ZR (ZI n) (Cons (Bool) (BTrue) (Cons (Bool) (BFalse) x))))))

(def-adts
  ((TR : ((Dorf) n) ((List (Bool)) x) -> Type)
    enum
    (many TRE : -> (TR (ZE) (Nil (Bool))))
    (many TRO : (erased (Dorf) n) (erased (List (Bool)) x) (erased (TR n x) z) -> (TR (ZO n) (Cons (Bool) (BFalse) (Cons (Bool) (BFalse) x))))
    (many TRI : (erased (Dorf) n) (erased (List (Bool)) x) (erased (TR n x) z)
       -> (TR (ZI n) (Cons (Bool) (BFalse) (Cons (Bool) (BTrue) (Cons (Bool) (BFalse) (Cons (Bool) (BTrue) x))))))))

(def-adts
  ((LR : ((Dorf) n) ((List (Bool)) x) -> Type)
    enum
    (many LRE : -> (LR (ZE) (Nil (Bool))))
    (many LRO : (erased (Dorf) n) (erased (List (Bool)) x) (erased (TR n x) z) -> (LR (ZO n) x))
    (many LRI : (erased (Dorf) n) (erased (List (Bool)) x) (erased (TR n x) z) -> (LR (ZI n) (Cons (Bool) (BFalse) (Cons (Bool) (BTrue) x))))))

(def-fns _ $ (erased zi-ex : (subterm erased (Dorf) n) -> (erased (Dorf) m) (erased (Zi n m) z))
  (let-match erased n (ZI n1) ((ZE) (values (ZI (ZE)) (ZiE))) ((ZO n1) (values (ZI n1) (ZiO n1))))
  (let ((erased m1) (erased z1)) (zi-ex n1))
  (values (ZO (ZO m1)) (ZiI n1 m1 z1)))

(let ((many p10)) (Cons _ (Def (Mov (BTrue) (DR) 1)) $ Cons _ (Def (Mov (BFalse) (DR) 0)) $ Cons _ (Def (Mov (BFalse) (DL) 2)) $ Cons _ (Def (Mov (BTrue) (DR) 0)) $
  Cons _ (Def (Mov (BTrue) (DR) 4)) $ Cons _ (Def (Mov (BTrue) (DL) 3)) $ Cons _ (Def (Mov (BTrue) (DL) 2)) $ Cons _ (Def (Mov (BFalse) (DL) 3)) $
  Cons _ (Undef) $ Cons _ (Def (Mov (BFalse) (DR) 1)) $ Nil (PT)))

(sk-family Sk10 MkSk10 sk10-of
  (sk10-r0 (1 DR "1" TV "" TZ) (3 DL "" TV "10" TZ))
  (sk10-r1 (1 DR "1" TV "0" TV) (3 DL "" TV "10" TV))
  (sk10-r2 (1 DR "1" TV "10" TV) (1 DR "111" TV "" TV))
  (sk10-r3 (3 DL "11" TV "" TV) (3 DL "" TV "00" TV))
  (sk10-l0 (3 DL "" TZ "11" TV) (0 DR "0101" TZ "" TV))
  (sk10-l1 (3 DL "00" TV "11" TV) (0 DR "0101" TV "" TV))
  (sk10-l2 (3 DL "0101" TV "11" TV) (3 DL "" TV "111111" TV))
  (sk10-l3 (0 DR "" TV "1111" TV) (0 DR "0000" TV "" TV))
  (sk10-d0 (3 DL "" TZ "10" TZ) (3 DL "01" TZ "010" TZ))
  (sk10-d1 (3 DL "00" TV "10" TV) (1 DR "1101" TV "" TV))
  (sk10-d2 (3 DL "101" TV "" TV) (3 DL "01" TV "0" TV))
  (sk10-d3 (3 DL "0101" TV "00" TV) (3 DL "" TV "111100" TV))
  (sk10-d4 (0 DR "" TV "1100" TV) (3 DL "00" TV "10" TV))
  (sk10-d5 (3 DL "01" TV "0" TV) (3 DL "" TV "110" TV))
  (sk10-d6 (0 DR "" TV "0" TV) (1 DR "1" TV "" TV))
  (sk10-i ((Zero) DR "" TZ "" TZ) (3 DL "" TZ "10" TZ)))
(comptime-match many (sk10-of p10) (ROk _ sg10))

(def-fns _ $ (erased sk10-right : (erased (Dorf) n m) (erased (List (Bool)) l x) (subterm erased (ZR n x) z) (erased (Zi n m) zi) ->
    (erased (List (Bool)) y) (erased (ZR m y) z2) (erased (Reach p10 (MkTc 1 (DR) (Cons (Bool) (BTrue) l) x) (MkTc 3 (DL) l y) (BTrue)) rc))
  (match erased z _
    ((ZRE) (let-match erased zi (ZiE)) (values (bits "10") (ZRI _ _ (ZRE)) (sk10-r0 p10 sg10 l x)))
    ((ZRO n1 x1 z1) (let-match erased zi (ZiO _)) (values (bits "10" x1) (ZRI _ _ z1) (sk10-r1 p10 sg10 l x1)))
    ((ZRI n1 x1 z1)
      (let-match erased zi (ZiI _ m1 zi1))
      (let ((erased y1) (erased z2) (erased r2)) (sk10-right n1 m1 (bits "11" l) x1 z1 zi1))
      (values (bits "00" y1) (ZRO _ _ (ZRO _ _ z2)) (reach-catT p10 _ _ _ _ (sk10-r2 p10 sg10 l x1) (reach-catT p10 _ _ _ _ r2 (sk10-r3 p10 sg10 l y1)))))))

(def-fns _ $ (erased sk10-left : (erased (Dorf) n m) (erased (List (Bool)) x r) (subterm erased (TR n x) t) (erased (Zi n m) zi) ->
    (erased (List (Bool)) y) (erased (TR m y) t2) (erased (Reach p10 (MkTc 3 (DL) x (bits "11" r)) (MkTc 0 (DR) y r) (BTrue)) rc))
  (match erased t _
    ((TRE) (let-match erased zi (ZiE)) (values (bits "0101") (TRI _ _ (TRE)) (sk10-l0 p10 sg10 x r)))
    ((TRO n1 x1 t1) (let-match erased zi (ZiO _)) (values (bits "0101" x1) (TRI _ _ t1) (sk10-l1 p10 sg10 x1 r)))
    ((TRI n1 x1 t1)
      (let-match erased zi (ZiI _ m1 zi1))
      (let ((erased y1) (erased t2) (erased r2)) (sk10-left n1 m1 x1 (bits "1111" r) t1 zi1))
      (values (bits "0000" y1) (TRO _ _ (TRO _ _ t2)) (reach-catT p10 _ _ _ _ (sk10-l2 p10 sg10 x1 r) (reach-catT p10 _ _ _ _ r2 (sk10-l3 p10 sg10 y1 r)))))))

(def-adts
  ((Inv10 : ((Tc) e) -> Type)
    enum
    (many MkI10 : (erased (Dorf) n m) (erased (List (Bool)) l r) (erased (LR n l) a) (erased (ZR m r) b) (erased (Inc n m) c) -> (Inv10 (MkTc 3 (DL) l r)))))

(def-fns _ $ (erased sk10-step : (erased (Tc) e) (erased (Inv10 e) iv) -> (erased (Tc) e2) (erased (Inv10 e2) iv2) (erased (Reach p10 e e2 (BTrue)) rc))
  (let-match erased iv (MkI10 n m l r a b c))
  (let ((erased base)) (MkI10 (ZI (ZE)) (ZO (ZI (ZE))) _ _ (LRI _ _ (TRE)) (ZRO _ _ (ZRI _ _ (ZRE))) (IncI _ _ (ZiE))))
  (match erased a _
    ((LRE)
      (let-match erased c (IncE))
      (let-match erased b (ZRI _ _ b1))
      (let-match erased b1 (ZRE))
      (values (MkTc 3 (DL) (bits "01") (bits "010")) base (sk10-d0 p10 sg10 l r)))
    ((LRO n0 x t)
      (let-match erased c (IncO _ _ zi))
      (match erased t _
        ((TRE)
          (let-match erased zi (ZiE))
          (let-match erased b (ZRI _ _ b1))
          (let-match erased b1 (ZRE))
          (values (MkTc 3 (DL) (bits "01") (bits "010")) base (sk10-d0 p10 sg10 l r)))
        ((TRO n1 x1 t1)
          (let-match erased zi (ZiO _))
          (let-match erased b (ZRI _ r1 b1))
          (let ((erased m1) (erased zi1)) (zi-ex n1))
          (let ((erased y) (erased z2) (erased r2)) (sk10-right n1 m1 (bits "101" x1) r1 b1 zi1))
          (values (MkTc 3 (DL) (bits "01" x1) (bits "0" y)) (MkI10 (ZI n1) (ZO m1) _ _ (LRI _ _ t1) (ZRO _ _ z2) (IncI _ _ zi1))
            (reach-catT p10 _ _ _ _ (sk10-d1 p10 sg10 x1 r1) (reach-catT p10 _ _ _ _ r2 (sk10-d2 p10 sg10 x1 y)))))
        ((TRI n1 x1 t1)
          (let-match erased zi (ZiI _ m1 zi1))
          (let-match erased b (ZRO _ _ b1))
          (let-match erased b1 (ZRO _ r1 b2))
          (let ((erased y) (erased t2) (erased r2)) (sk10-left n1 m1 x1 (bits "1100" r1) t1 zi1))
          (values (MkTc 3 (DL) (bits "00" y) (bits "10" r1)) (MkI10 (ZO (ZO m1)) (ZI m1) _ _ (LRO _ _ (TRO _ _ t2)) (ZRI _ _ b2) (IncO _ _ (ZiO _)))
            (reach-catT p10 _ _ _ _ (sk10-d3 p10 sg10 x1 r1) (reach-catT p10 _ _ _ _ r2 (sk10-d4 p10 sg10 y r1)))))))
    ((LRI n0 x0 t)
      (let-match erased c (IncI _ m0 zi))
      (let-match erased b (ZRO _ r0 b0))
      (let ((erased y) (erased t2) (erased r2)) (sk10-left n0 m0 x0 (bits "0" r0) t zi))
      (let ((erased m2) (erased zi2)) (zi-ex m0))
      (let ((erased y2) (erased z3) (erased r4)) (sk10-right m0 m2 y r0 b0 zi2))
      (values (MkTc 3 (DL) y y2) (MkI10 (ZO m0) m2 _ _ (LRO _ _ t2) z3 (IncO _ _ zi2))
        (reach-catT p10 _ _ _ _ (sk10-d5 p10 sg10 x0 r0) (reach-catT p10 _ _ _ _ r2 (reach-catT p10 _ _ _ _ (sk10-d6 p10 sg10 y r0) r4)))))))

(def-fns _ $ (erased absurd sk10-loop : (erased (List (Tr)) m) (erased (Ext p10 m) ex) (erased (Tc) e) (erased (Inv10 e) iv) (erased (Conf) c) (erased (AsC e c) ac)
    (subterm erased (Nat) u) (erased (HaltsAt m c u) hs) -> (erased (False) f))
  (let ((erased e2) (erased iv2) (erased rc)) (sk10-step e iv))
  (let ((erased c2) (erased ac2) (erased v) (erased hd) (erased lt)) (reach-halts p10 m ex e e2 c u rc ac hs))
  (sk10-loop m ex e2 iv2 c2 ac2 (subterm (lt-subterm v u lt)) v hd))

(def-fns _ $ (erased absurd never-sk10 : (erased (List (Tr)) m) (erased (Ext p10 m) ex)
    (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
  (let ((erased c0)) (MkAsC (Zero) (DR) _ _ _ _ _ _ _ (BFalse) (OrR _ (Nil (Bool)) (Nil (Bool))) (PullNil) (OrR _ (Nil (Bool)) (Nil (Bool)))))
  (let ((erased c2) (erased ac2) (erased v) (erased hd) (erased lt)) (reach-halts p10 m ex _ _ _ s (sk10-i p10 sg10 (Nil (Bool)) (Nil (Bool))) c0 hs))
  (sk10-loop m ex _ (MkI10 (ZE) (ZI (ZE)) _ _ (LRE) (ZRI _ _ (ZRE)) (IncE)) c2 ac2 v hd))

(def-fns _ $ (erased le-tr : (erased (Nat) a b c) (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a (Succ c)) r))
  (lt-le-trans a (Succ b) (Succ c) p (LtS b (Succ c) q)))

(def-fns _ $ (erased add-mono : (erased (Nat) a b x c d) (subterm erased (Add a x c) p) (erased (Add b x d) q) (erased (Lt a (Succ b)) le)
    -> (erased (Lt c (Succ d)) r))
  (let-match erased p (AddSucc a1 _ c1 p1) ((AddZero _) (add-le-left x b d (add-comm b x d q))))
  (let-match erased le (LtS _ _ le1))
  (let-match erased b (Succ b1) (absurd (Zero) le1))
  (let-match erased q (AddSucc _ _ d1 q1))
  (LtS c1 (Succ d1) (add-mono a1 b1 x c1 d1 p1 q1 le1)))

(def-fns _ $ (erased add-mono-2 : (erased (Nat) a b c d) (erased (Add a a c) p) (erased (Add b b d) q) (erased (Lt a (Succ b)) le)
    -> (erased (Lt c (Succ d)) r))
  (let ((erased e) (erased ae)) (add-ex b a))
  (le-tr c e d (add-mono a b a c e p ae le) (add-mono a b b e d (add-comm b a e ae) q le)))

(def-fns _ $ (erased add-cancel-le : (erased (Nat) z u v w c) (subterm erased (Add z u v) p) (erased (Add z w c) q) (erased (Lt v (Succ c)) le)
    -> (erased (Lt u (Succ w)) r))
  (let-match erased p (AddSucc z1 _ v1 p1) ((AddZero _) (let-match erased q (AddZero _)) le))
  (let-match erased q (AddSucc _ _ c1 q1))
  (let-match erased le (LtS _ _ le1))
  (add-cancel-le z1 u v1 w c1 p1 q1 le1))

(def-fns _ $ (erased diag-add : (erased (Nat) z u s v dz du) (subterm erased (Add z u s) p) (erased (Add s s v) ps) (erased (Add z z dz) pz) (erased (Add u u du) pu)
    -> (erased (Add dz du v) r))
  (let-match erased p (AddSucc z1 _ s1 p1)
    ((AddZero _) (let-match erased pz (AddZero _)) (let-match erased (add-fn u u v du ps pu) (Refl _ _)) (AddZero du)))
  (let-match erased ps (AddSucc _ _ v1 ps1))
  (let ((erased v2) (erased e1) (erased ps2)) (add-succ-right-inv s1 s1 v1 ps1))
  (let-match erased e1 (Refl _ _))
  (let-match erased pz (AddSucc _ _ dz1 pz1))
  (let ((erased dz2) (erased e2) (erased pz2)) (add-succ-right-inv z1 z1 dz1 pz1))
  (let-match erased e2 (Refl _ _))
  (AddSucc (Succ dz2) du (Succ v2) (AddSucc dz2 du v2 (diag-add z1 u s1 v2 dz2 du p1 ps2 pz2 pu))))

(def-adts
  ((Wc : ((List (Bool)) xs) ((List (Bool)) ys) -> Type)
    enum
    (many WcF : (erased (List (Bool)) xs) -> (Wc (Cons (Bool) (BFalse) xs) (Cons (Bool) (BTrue) xs)))
    (many WcT : (erased (List (Bool)) xs ys) (erased (Wc xs ys) w) -> (Wc (Cons (Bool) (BTrue) xs) (Cons (Bool) (BFalse) ys)))))

(def-adts
  ((Ov : ((List (Bool)) xs) ((List (Bool)) ys) -> Type)
    enum
    (many OvN : -> (Ov (Nil (Bool)) (bits "0")))
    (many OvT : (erased (List (Bool)) xs ys) (erased (Ov xs ys) o) -> (Ov (Cons (Bool) (BTrue) xs) (Cons (Bool) (BFalse) ys)))))

(def-adts
  ((Bc : ((List (Bool)) xs) ((Nat) c) -> Type)
    enum
    (many BcN : -> (Bc (Nil (Bool)) (Zero)))
    (many BcF : (erased (List (Bool)) xs) (erased (Nat) c d) (erased (Bc xs c) b) (erased (Add c c d) a) -> (Bc (Cons (Bool) (BFalse) xs) (Succ d)))
    (many BcT : (erased (List (Bool)) xs) (erased (Nat) c d) (erased (Bc xs c) b) (erased (Add c c d) a) -> (Bc (Cons (Bool) (BTrue) xs) d))))

(def-adts
  ((PV : ((List (Bool)) xs) ((Nat) v) -> Type)
    enum
    (many PVN : -> (PV (Nil (Bool)) (Succ (Zero))))
    (many PVF : (erased (List (Bool)) xs) (erased (Nat) v w) (erased (PV xs v) b) (erased (Add v v w) a) -> (PV (Cons (Bool) (BFalse) xs) w))
    (many PVT : (erased (List (Bool)) xs) (erased (Nat) v w) (erased (PV xs v) b) (erased (Add v v w) a) -> (PV (Cons (Bool) (BTrue) xs) (Succ w)))))

(def-adts
  ((Fz : ((List (Bool)) xs) ((List (Bool)) zs) -> Type)
    enum
    (many FzN : -> (Fz (Nil (Bool)) (Nil (Bool))))
    (many FzC : (erased (Bool) b) (erased (List (Bool)) xs zs) (erased (Fz xs zs) f) -> (Fz (Cons (Bool) b xs) (Cons (Bool) (BFalse) zs)))))

(def-fns _ $ (erased bc-ex : (subterm erased (List (Bool)) xs) -> (erased (Nat) c) (erased (Bc xs c) b))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values (Zero) (BcN))))
  (let ((erased c1) (erased b1)) (bc-ex xs1))
  (let ((erased d) (erased a)) (add-ex c1 c1))
  (match erased x (((Nat) c) ((Bc xs c) b))
    ((BFalse) (values (Succ d) (BcF xs1 c1 d b1 a)))
    ((BTrue) (values d (BcT xs1 c1 d b1 a)))))

(def-fns _ $ (erased bc-fn : (erased (List (Bool)) xs) (erased (Nat) c c2) (subterm erased (Bc xs c) b) (erased (Bc xs c2) b2) -> (erased (Eq (Nat) c c2) e))
  (match erased b _
    ((BcN) (let-match erased b2 (BcN)) (Refl (Nat) c))
    ((BcF xs1 c1 d b1 a)
      (let-match erased b2 (BcF _ c3 d3 b3 a3))
      (let-match erased (bc-fn xs1 c1 c3 b1 b3) (Refl _ _))
      (let-match erased (add-fn c1 c1 d d3 a a3) (Refl _ _))
      (Refl (Nat) c))
    ((BcT xs1 c1 d b1 a)
      (let-match erased b2 (BcT _ c3 d3 b3 a3))
      (let-match erased (bc-fn xs1 c1 c3 b1 b3) (Refl _ _))
      (let-match erased (add-fn c1 c1 d d3 a a3) (Refl _ _))
      (Refl (Nat) c))))

(def-fns _ $ (erased bc-cons-ge : (erased (List (Bool)) xs) (erased (Bool) x) (erased (Nat) c c2) (erased (Bc xs c) b) (erased (Bc (Cons (Bool) x xs) c2) b2)
    -> (erased (Lt c (Succ c2)) r))
  (match erased b2 _
    ((BcF _ c1 d b1 a) (let-match erased (bc-fn xs c c1 b b1) (Refl _ _)) (lt-weaken c (Succ d) (add-le-left c c d a)))
    ((BcT _ c1 d b1 a) (let-match erased (bc-fn xs c c1 b b1) (Refl _ _)) (add-le-left c c d a))))

(def-fns _ $ (erased w-ex : (erased (List (Bool)) xs) (erased (Nat) c) (subterm erased (Bc xs (Succ c)) b) -> (erased (List (Bool)) ys) (erased (Wc xs ys) w) (erased (Bc ys c) b2))
  (let-match erased b (BcT xs1 c1 d b1 a) ((BcF xs1 c1 d b1 a) (values (Cons (Bool) (BTrue) xs1) (WcF xs1) (BcT xs1 c1 d b1 a))))
  (let-match erased a (AddSucc c2 _ _ a2))
  (let ((erased c3) (erased e) (erased a3)) (add-succ-right-inv c2 c2 c a2))
  (let-match erased e (Refl _ _))
  (let ((erased ys1) (erased w1) (erased bc1)) (w-ex xs1 c2 b1))
  (values (Cons (Bool) (BFalse) ys1) (WcT xs1 ys1 w1) (BcF ys1 c2 c3 bc1 a3)))

(def-fns _ $ (erased ov-ex : (erased (List (Bool)) xs) (subterm erased (Bc xs (Zero)) b) -> (erased (List (Bool)) zs) (erased (Ov xs (Cons (Bool) (BFalse) zs)) o) (erased (Fz xs zs) f))
  (let-match erased b (BcT xs1 c1 d b1 a) ((BcN) (values (Nil (Bool)) (OvN) (FzN))))
  (let-match erased a (AddZero _))
  (let ((erased zs1) (erased o1) (erased f1)) (ov-ex xs1 b1))
  (values (Cons (Bool) (BFalse) zs1) (OvT xs1 (Cons (Bool) (BFalse) zs1) o1) (FzC (BTrue) xs1 zs1 f1)))

(def-fns _ $ (erased fz-ex : (subterm erased (List (Bool)) xs) -> (erased (List (Bool)) zs) (erased (Fz xs zs) f))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (values (Nil (Bool)) (FzN))))
  (let ((erased zs1) (erased f1)) (fz-ex xs1))
  (values (Cons (Bool) (BFalse) zs1) (FzC x xs1 zs1 f1)))

(def-fns _ $ (erased fz-fn : (erased (List (Bool)) xs zs zs2) (subterm erased (Fz xs zs) f) (erased (Fz xs zs2) f2) -> (erased (Eq (List (Bool)) zs zs2) e))
  (let-match erased f (FzC b xs1 zs1 f1) ((FzN) (let-match erased f2 (FzN)) (Refl _ zs)))
  (let-match erased f2 (FzC _ _ zs3 f3))
  (let-match erased (fz-fn xs1 zs1 zs3 f1 f3) (Refl _ _))
  (Refl _ zs))

(def-fns _ $ (erased w-fz : (erased (List (Bool)) xs ys zs) (subterm erased (Wc xs ys) w) (erased (Fz xs zs) f) -> (erased (Fz ys zs) f2))
  (match erased w _
    ((WcF xs1) (let-match erased f (FzC _ _ zs1 f1)) (FzC (BTrue) xs1 zs1 f1))
    ((WcT xs1 ys1 w1) (let-match erased f (FzC _ _ zs1 f1)) (FzC (BFalse) ys1 zs1 (w-fz xs1 ys1 zs1 w1 f1)))))

(def-fns _ $ (erased bc-fz : (erased (List (Bool)) xs zs) (erased (Nat) c z) (subterm erased (Fz xs zs) f) (erased (Bc xs c) b) (erased (Bc zs z) bz)
    -> (erased (Lt c (Succ z)) r))
  (let-match erased f (FzC x xs1 zs1 f1) ((FzN) (let-match erased b (BcN)) (let-match erased bz (BcN)) (LtZ (Zero))))
  (let-match erased bz (BcF _ z1 d bz1 az))
  (match erased b _
    ((BcF _ c1 dc b1 ac) (LtS dc (Succ d) (add-mono-2 c1 z1 dc d ac az (bc-fz xs1 zs1 c1 z1 f1 b1 bz1))))
    ((BcT _ c1 dc b1 ac) (lt-weaken dc (Succ d) (add-mono-2 c1 z1 dc d ac az (bc-fz xs1 zs1 c1 z1 f1 b1 bz1))))))

(def-adts
  ((RR : ((List (Bool)) ms) ((List (Bool)) x) -> Type)
    enum
    (many RRN : -> (RR (Nil (Bool)) (bits "11")))
    (many RRC : (erased (Bool) b) (erased (List (Bool)) ms x) (erased (RR ms x) r) -> (RR (Cons (Bool) b ms) (Cons (Bool) (BTrue) (Cons (Bool) b x))))))

(def-adts
  ((KR : ((List (Bool)) bs) ((List (Bool)) x) -> Type)
    enum
    (many KRN : -> (KR (Nil (Bool)) (bits "001")))
    (many KRF : (erased (List (Bool)) bs x) (erased (KR bs x) k) -> (KR (Cons (Bool) (BFalse) bs) (bits "0000" x)))
    (many KRT : (erased (List (Bool)) bs x) (erased (KR bs x) k) -> (KR (Cons (Bool) (BTrue) bs) (bits "0010" x)))))

(def-adts
  ((LkR : ((List (Bool)) cs) ((List (Bool)) t) ((List (Bool)) x) -> Type)
    enum
    (many LkN : (erased (List (Bool)) t) -> (LkR (Nil (Bool)) t t))
    (many LkC : (erased (Bool) b) (erased (List (Bool)) cs t x) (erased (LkR cs t x) k)
       -> (LkR (Cons (Bool) b cs) t (bits "000" (Cons (Bool) b x))))))

(def-adts $ (Cn : -> Type)
  enum
  (many N0 : -> (Cn))
  (many NP : (many (List (Bool)) bs) -> (Cn)))

(def-adts
  ((LnR : ((Cn) n) ((List (Bool)) x) -> Type)
    enum
    (many LnR0 : -> (LnR (N0) (Nil (Bool))))
    (many LnRP : (erased (List (Bool)) bs x) (erased (KR bs x) k) -> (LnR (NP bs) (Cons (Bool) (BFalse) x)))))

(def-adts
  ((NV : ((Cn) n) ((Nat) v) -> Type)
    enum
    (many NV0 : -> (NV (N0) (Zero)))
    (many NVP : (erased (List (Bool)) bs) (erased (Nat) v) (erased (PV bs v) p) -> (NV (NP bs) v))))

(sk-family So34 MkSo34 so34-of
  (so-l0 (2 DL "" TZ "" TV) (1 DR "0001" TZ "" TV))
  (so-l1 (2 DL "0001" TZ "" TV) (1 DR "00000001" TZ "" TV))
  (so-c0 (2 DL "0000" TV "" TV) (1 DR "0001" TV "" TV))
  (so-c1 (2 DL "0001" TV "" TV) (2 DL "" TV "1111" TV))
  (so-c2 (1 DR "" TV "1111" TV) (1 DR "0000" TV "" TV))
  (so-h0 (2 DR "0" TV "10" TV) (0 DL "" TV "011" TV))
  (so-h1 (2 DR "0" TV "11" TV) (2 DR "011" TV "" TV))
  (so-h2 (0 DL "11" TV "0" TV) (0 DL "" TV "010" TV))
  (so-a0 (2 DR "0" TV "11" TZ) (2 DL "" TV "1011" TZ))
  (so-a1 (2 DL "11" TV "" TV) (2 DL "" TV "10" TV))
  (so-d0 (1 DR "" TV "1010" TV) (2 DR "0111" TV "" TV))
  (so-d1 (0 DL "111" TV "0" TV) (2 DL "" TV "1010" TV))
  (so-s0 (2 DL "1110" TV "" TV) (2 DL "" TV "1011" TV))
  (so-e0 (1 DR "" TV "1011" TV) (2 DR "0110" TV "" TV))
  (so-e1 (0 DL "110" TV "0" TV) (2 DL "" TV "1011" TV))
  (so-k0 (2 DL "0010" TV "" TV) (2 DR "0111" TV "" TV))
  (so-k1 (2 DL "001" TZ "" TV) (2 DR "0111" TZ "" TV))
  (so-i0 ((Zero) DR "" TZ "" TZ) (2 DL "" TZ "10101110101010111011111011" TZ)))

(def-fns _ $ (erased kc-inc : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Bool)) bs K r) (erased (Nat) v) (subterm erased (KR bs K) kr) (erased (PV bs v) pv)
    -> (erased (List (Bool)) bs2 K2) (erased (PV bs2 (Succ v)) pv2) (erased (KR bs2 K2) kr2)
    (erased (Reach p (MkTc 2 (DL) (Cons (Bool) (BFalse) K) r) (MkTc 1 (DR) (Cons (Bool) (BFalse) K2) r) (BTrue)) rc))
  (match erased kr _
    ((KRN)
      (let-match erased pv (PVN))
      (values (bits "0") (bits "0000001") (PVF _ _ _ (PVN) (AddSucc (Zero) (Succ (Zero)) (Succ (Zero)) (AddZero (Succ (Zero))))) (KRF _ _ (KRN)) (so-l1 p sg (Nil (Bool)) r)))
    ((KRF bs1 X kr1)
      (let-match erased pv (PVF _ v1 _ pv1 a))
      (values (Cons (Bool) (BTrue) bs1) (bits "0010" X) (PVT bs1 v1 v pv1 a) (KRT _ _ kr1) (so-c0 p sg (Cons (Bool) (BFalse) X) r)))
    ((KRT bs1 X kr1)
      (let-match erased pv (PVT _ v1 w pv1 a))
      (let ((erased bs3) (erased X3) (erased pv3) (erased kr3) (erased rc)) (kc-inc p sg bs1 X (bits "1111" r) v1 kr1 pv1))
      (values (Cons (Bool) (BFalse) bs3) (bits "0000" X3) (PVF bs3 (Succ v1) (Succ (Succ w)) pv3 (AddSucc v1 (Succ v1) (Succ w) (add-succ-right v1 v1 w a)))
        (KRF _ _ kr3)
        (reach-catT p _ _ _ _ (so-c1 p sg (Cons (Bool) (BFalse) X) r) (reach-catT p _ _ _ _ rc (so-c2 p sg (Cons (Bool) (BFalse) X3) r)))))))

(def-fns _ $ (erased l-inc : (erased (List (PT)) p) (erased (So34 p) sg) (erased (Cn) n) (erased (Nat) v) (erased (List (Bool)) X r) (erased (NV n v) nv) (erased (LnR n X) lr)
    -> (erased (Cn) n2) (erased (List (Bool)) X2) (erased (NV n2 (Succ v)) nv2) (erased (LnR n2 X2) lr2)
    (erased (Reach p (MkTc 2 (DL) X r) (MkTc 1 (DR) X2 r) (BTrue)) rc))
  (match erased nv _
    ((NV0) (let-match erased lr (LnR0)) (values (NP (Nil (Bool))) (bits "0001") (NVP _ _ (PVN)) (LnRP _ _ (KRN)) (so-l0 p sg (Nil (Bool)) r)))
    ((NVP bs _ pv)
      (let-match erased lr (LnRP _ K kr))
      (let ((erased bs2) (erased K2) (erased pv2) (erased kr2) (erased rc)) (kc-inc p sg bs K r v kr pv))
      (values (NP bs2) (Cons (Bool) (BFalse) K2) (NVP _ _ pv2) (LnRP _ _ kr2) rc))))

(def-fns _ $ (erased lk-inc : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Bool)) cs cs2 t X r) (subterm erased (Wc cs cs2) w) (erased (LkR cs t X) lk)
    -> (erased (List (Bool)) X2) (erased (LkR cs2 t X2) lk2) (erased (Reach p (MkTc 2 (DL) X r) (MkTc 1 (DR) X2 r) (BTrue)) rc))
  (match erased w _
    ((WcF xs) (let-match erased lk (LkC _ _ _ X1 lk1)) (values (bits "0001" X1) (LkC (BTrue) xs t X1 lk1) (so-c0 p sg X1 r)))
    ((WcT xs ys w1)
      (let-match erased lk (LkC _ _ _ X1 lk1))
      (let ((erased X3) (erased lk3) (erased rc)) (lk-inc p sg xs ys t X1 (bits "1111" r) w1 lk1))
      (values (bits "0000" X3) (LkC (BFalse) ys t X3 lk3)
        (reach-catT p _ _ _ _ (so-c1 p sg X1 r) (reach-catT p _ _ _ _ rc (so-c2 p sg X3 r)))))))

(def-fns _ $ (erased r-inc : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Bool)) ms ms2 X l) (subterm erased (Wc ms ms2) w) (erased (RR ms X) rr)
    -> (erased (List (Bool)) X2) (erased (RR ms2 X2) rr2) (erased (Reach p (MkTc 2 (DR) (Cons (Bool) (BFalse) l) X) (MkTc 0 (DL) l (Cons (Bool) (BFalse) X2)) (BTrue)) rc))
  (match erased w _
    ((WcF xs) (let-match erased rr (RRC _ _ X1 rr1)) (values (bits "11" X1) (RRC (BTrue) xs X1 rr1) (so-h0 p sg l X1)))
    ((WcT xs ys w1)
      (let-match erased rr (RRC _ _ X1 rr1))
      (let ((erased X3) (erased rr3) (erased rc)) (r-inc p sg xs ys X1 (bits "11" l) w1 rr1))
      (values (bits "10" X3) (RRC (BFalse) ys X3 rr3)
        (reach-catT p _ _ _ _ (so-h1 p sg l X1) (reach-catT p _ _ _ _ rc (so-h2 p sg l X3)))))))

(def-fns _ $ (erased r-ov : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Bool)) ms ms2 X l) (subterm erased (Ov ms ms2) o) (erased (RR ms X) rr)
    -> (erased (List (Bool)) X2) (erased (RR ms2 X2) rr2) (erased (Reach p (MkTc 2 (DR) (Cons (Bool) (BFalse) l) X) (MkTc 2 (DL) l X2) (BTrue)) rc))
  (match erased o _
    ((OvN) (let-match erased rr (RRN)) (values (bits "1011") (RRC (BFalse) _ _ (RRN)) (so-a0 p sg l (Nil (Bool)))))
    ((OvT xs ys o1)
      (let-match erased rr (RRC _ _ X1 rr1))
      (let ((erased X3) (erased rr3) (erased rc)) (r-ov p sg xs ys X1 (bits "11" l) o1 rr1))
      (values (bits "10" X3) (RRC (BFalse) ys X3 rr3)
        (reach-catT p _ _ _ _ (so-h1 p sg l X1) (reach-catT p _ _ _ _ rc (so-a1 p sg l X3)))))))

(def-fns _ $ (erased la-step : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Bool)) X X2 ms ms2 R) (erased (Bool) a)
    (erased (Reach p (MkTc 2 (DL) X (bits "101" (Cons (Bool) a R))) (MkTc 1 (DR) X2 (bits "101" (Cons (Bool) a R))) (BTrue)) rc) (erased (Wc ms ms2) w) (erased (RR ms R) rr)
    -> (erased (List (Bool)) R2) (erased (RR ms2 R2) rr2) (erased (Reach p (MkTc 2 (DL) X (bits "101" (Cons (Bool) a R))) (MkTc 2 (DL) X2 (bits "101" (Cons (Bool) a R2))) (BTrue)) rc2))
  (match erased a _
    ((BFalse)
      (let ((erased R2) (erased rr2) (erased rc1)) (r-inc p sg ms ms2 R (bits "111" X2) w rr))
      (values R2 rr2 (reach-catT p _ _ _ _ rc (reach-catT p _ _ _ _ (so-d0 p sg X2 R) (reach-catT p _ _ _ _ rc1 (so-d1 p sg X2 R2))))))
    ((BTrue)
      (let ((erased R2) (erased rr2) (erased rc1)) (r-inc p sg ms ms2 R (bits "110" X2) w rr))
      (values R2 rr2 (reach-catT p _ _ _ _ rc (reach-catT p _ _ _ _ (so-e0 p sg X2 R) (reach-catT p _ _ _ _ rc1 (so-e1 p sg X2 R2))))))))

(def-fns _ $ (erased d-run : (erased (List (PT)) p) (erased (So34 p) sg) (subterm erased (Nat) c) (erased (Cn) n) (erased (Nat) v) (erased (List (Bool)) X ms R zs)
    (erased (NV n v) nv) (erased (LnR n X) lr) (erased (RR ms R) rr) (erased (Bc ms c) bc) (erased (Fz ms zs) fz)
    -> (erased (Cn) n2) (erased (Nat) v2) (erased (List (Bool)) X2 ms2 R2) (erased (Bool) g)
    (erased (NV n2 v2) nv2) (erased (Add c v v2) ad) (erased (LnR n2 X2) lr2) (erased (RR ms2 R2) rr2) (erased (Bc ms2 (Zero)) bc2) (erased (Fz ms2 zs) fz2)
    (erased (Reach p (MkTc 2 (DL) X (bits "1010" R)) (MkTc 2 (DL) X2 (bits "1010" R2)) g) rc))
  (let-match erased c (Succ c1) ((Zero) (values n v X ms R (BFalse) nv (AddZero v) lr rr bc fz (reach-refl p _))))
  (let ((erased ms1) (erased w) (erased bc1)) (w-ex ms c1 bc))
  (let ((erased n1) (erased X1) (erased nv1) (erased lr1) (erased rc1)) (l-inc p sg n v X (bits "1010" R) nv lr))
  (let ((erased R1) (erased rr1) (erased rc2)) (la-step p sg X X1 ms ms1 R (BFalse) rc1 w rr))
  (let ((erased n2) (erased v2) (erased X2) (erased ms2) (erased R2) (erased g) (erased nv2) (erased ad) (erased lr2) (erased rr2) (erased bc2) (erased fz2) (erased rc3))
    (d-run p sg c1 n1 (Succ v) X1 ms1 R1 zs nv1 lr1 rr1 bc1 (w-fz ms ms1 zs w fz)))
  (values n2 v2 X2 ms2 R2 (BTrue) nv2 (add-shift c1 v v2 ad) lr2 rr2 bc2 fz2 (reach-catT p _ _ _ _ rc2 rc3)))

(def-fns _ $ (erased la-run : (erased (List (PT)) p) (erased (So34 p) sg) (subterm erased (Nat) z) (erased (List (Bool)) cs t X ms R) (erased (Bool) a) (erased (Nat) c)
    (erased (LkR cs t X) lk) (erased (Bc cs z) bz) (erased (RR ms R) rr) (erased (Bc ms c) bc) (erased (Lt z (Succ c)) le)
    -> (erased (List (Bool)) cs2 X2 ms2 R2) (erased (Nat) c2) (erased (Bool) g)
    (erased (LkR cs2 t X2) lk2) (erased (Bc cs2 (Zero)) bz2) (erased (RR ms2 R2) rr2) (erased (Bc ms2 c2) bc2) (erased (Add z c2 c) ad)
    (erased (Reach p (MkTc 2 (DL) X (bits "101" (Cons (Bool) a R))) (MkTc 2 (DL) X2 (bits "101" (Cons (Bool) a R2))) g) rc))
  (let-match erased z (Succ z1) ((Zero) (values cs X ms R c (BFalse) lk bz rr bc (AddZero c) (reach-refl p _))))
  (let-match erased le (LtS _ _ le1))
  (let-match erased c (Succ c1) (absurd (Zero) le1))
  (let ((erased cs1) (erased w1) (erased bz1)) (w-ex cs z1 bz))
  (let ((erased ms1) (erased w2) (erased bc1)) (w-ex ms c1 bc))
  (let ((erased X1) (erased lk1) (erased rc1)) (lk-inc p sg cs cs1 t X (bits "101" (Cons (Bool) a R)) w1 lk))
  (let ((erased R1) (erased rr1) (erased rc2)) (la-step p sg X X1 ms ms1 R a rc1 w2 rr))
  (let ((erased cs2) (erased X2) (erased ms2) (erased R2) (erased c2) (erased g) (erased lk2) (erased bz2) (erased rr2) (erased bc2) (erased ad) (erased rc3))
    (la-run p sg z1 cs1 t X1 ms1 R1 a c1 lk1 bz1 rr1 bc1 le1))
  (values cs2 X2 ms2 R2 c2 (BTrue) lk2 bz2 rr2 bc2 (AddSucc z1 c2 c1 ad) (reach-catT p _ _ _ _ rc2 rc3)))

(def-fns _ $ (erased eat-max : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Bool)) cs t X ts R) (erased (Nat) c)
    (subterm erased (LkR cs t X) lk) (erased (Bc cs (Zero)) bz) (erased (RR ts R) rr) (erased (Bc ts c) bc)
    -> (erased (List (Bool)) ts2 R2) (erased (Nat) c2) (erased (Bool) g) (erased (RR ts2 R2) rr2) (erased (Bc ts2 c2) bc2) (erased (Lt c (Succ c2)) le)
    (erased (Reach p (MkTc 2 (DL) X R) (MkTc 2 (DL) t R2) g) rc))
  (let-match erased lk (LkC b cs1 _ X1 lk1) ((LkN _) (values ts R c (BFalse) rr bc (lt-succ c) (reach-refl p _))))
  (let-match erased bz (BcT _ z1 _ bz1 az))
  (let-match erased az (AddZero _))
  (let ((erased d) (erased ad)) (add-ex c c))
  (let ((erased e) (erased ae)) (add-ex d d))
  (let ((erased ts2) (erased R2) (erased c2) (erased g) (erased rr2) (erased bc2) (erased le) (erased rc))
    (eat-max p sg cs1 t X1 (bits "11" ts) (bits "1111" R) e lk1 bz1 (RRC _ _ _ (RRC _ _ _ rr)) (BcT _ d e (BcT _ c d bc ad) ae)))
  (values ts2 R2 c2 (BTrue) rr2 bc2 (le-tr c d c2 (add-le-left c c d ad) (le-tr d e c2 (add-le-left d d e ae) le))
    (reach-catT p _ _ _ _ (so-c1 p sg X1 R) rc)))

(def-adts
  ((KSp : ((List (Bool)) K) ((Nat) v) -> Type)
    enum
    (many KS1 : (erased (List (Bool)) cs K) (erased (Nat) z) (erased (LkR cs (bits "001") K) lk) (erased (Bc cs z) b) -> (KSp K (Succ z)))
    (many KS2 : (erased (List (Bool)) cs K bs2 K2) (erased (Nat) z w v v2) (erased (LkR cs (bits "0010" K2) K) lk) (erased (Bc cs z) b)
       (erased (KR bs2 K2) kr) (erased (PV bs2 v2) pv) (erased (Add z w v) a) (erased (Lt v2 w) lt) -> (KSp K v))))

(def-fns _ $ (erased kr-split : (erased (List (Bool)) bs K) (erased (Nat) v) (subterm erased (KR bs K) kr) (erased (PV bs v) pv) -> (erased (KSp K v) ks))
  (match erased kr _
    ((KRN) (let-match erased pv (PVN)) (KS1 (Nil (Bool)) K (Zero) (LkN K) (BcN)))
    ((KRT bs2 K2 kr2)
      (let-match erased pv (PVT _ v2 w pv2 a))
      (KS2 (Nil (Bool)) K bs2 K2 (Zero) v v v2 (LkN K) (BcN) kr2 pv2 (AddZero v) (add-le-left v2 v2 w a)))
    ((KRF bs1 X kr1)
      (let-match erased pv (PVF _ v1 _ pv1 a))
      (let ((erased ks)) (kr-split bs1 X v1 kr1 pv1))
      (match erased ks _
        ((KS1 cs _ z lk b)
          (let-match erased a (AddSucc _ _ v3 a1))
          (let ((erased dz) (erased e) (erased adz)) (add-succ-right-inv z z v3 a1))
          (let-match erased e (Refl _ _))
          (KS1 (Cons (Bool) (BFalse) cs) K (Succ dz) (LkC (BFalse) cs _ X lk) (BcF cs z dz b adz)))
        ((KS2 cs _ bs2 K2 z w _ v2 lk b kr2 pv2 azw lt)
          (let-match erased w (Succ w1) (absurd (Zero) lt))
          (let ((erased dz) (erased adz)) (add-ex z z))
          (let ((erased du) (erased adu)) (add-ex w w))
          (let ((erased ad)) (diag-add z w v1 v dz du azw a adz adu))
          (let-match erased adu (AddSucc _ _ du1 adu1))
          (let ((erased e1) (erased eq) (erased ae)) (add-succ-right-inv w1 w1 du1 adu1))
          (let-match erased eq (Refl _ _))
          (KS2 (Cons (Bool) (BFalse) cs) K bs2 K2 (Succ dz) (Succ e1) v v2 (LkC (BFalse) cs _ X lk) (BcF cs z dz b adz) kr2 pv2
            (add-shift dz (Succ e1) v ad) (le-tr v2 w1 e1 lt (add-le-left w1 w1 e1 ae))))))))

(def-fns _ $ (erased reset-pre : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Bool)) cs t K ms R) (erased (Bool) a) (erased (Nat) z c)
    (erased (LkR cs t K) lk) (erased (Bc cs z) bz) (erased (RR ms R) rr) (erased (Bc ms c) bc) (erased (Lt z (Succ c)) le)
    -> (erased (List (Bool)) ts R3) (erased (Nat) c4 c2) (erased (Bool) g) (erased (RR ts R3) rr3) (erased (Bc ts (Succ c4)) bc3)
    (erased (Add z c2 c) ad) (erased (Lt c2 (Succ c4)) le2) (erased (Reach p (MkTc 2 (DL) K (bits "101" (Cons (Bool) a R))) (MkTc 2 (DL) t R3) g) rc))
  (let ((erased cs2) (erased X2) (erased ms2) (erased R2) (erased c2) (erased g1) (erased lk2) (erased bz2) (erased rr2) (erased bc2) (erased ad) (erased rc1))
    (la-run p sg z cs t K ms R a c lk bz rr bc le))
  (let ((erased ca) (erased bca)) (bc-ex (Cons (Bool) a ms2)))
  (let ((erased dd) (erased aca)) (add-ex ca ca))
  (let ((erased ts) (erased R3) (erased c3) (erased g2) (erased rr3) (erased bc3) (erased le3) (erased rc2))
    (eat-max p sg cs2 t X2 (Cons (Bool) (BFalse) (Cons (Bool) a ms2)) (bits "101" (Cons (Bool) a R2)) (Succ dd) lk2 bz2
      (RRC (BFalse) _ _ (RRC a _ _ rr2)) (BcF (Cons (Bool) a ms2) ca dd bca aca)))
  (let-match erased le3 (LtS _ _ le4))
  (let-match erased c3 (Succ c4) (absurd (Zero) le4))
  (let ((erased g) (erased o) (erased rc)) (reach-cat p _ _ _ g1 g2 rc1 rc2))
  (values ts R3 c4 c2 g rr3 bc3 ad (le-tr c2 ca c4 (bc-cons-ge ms2 a c2 ca bc2 bca) (le-tr ca dd c4 (add-le-left ca ca dd aca) le4)) rc))

(def-fns _ $ (erased reset-post : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Bool)) L R3 ts) (erased (Nat) c4) (erased (RR ts R3) rr3) (erased (Bc ts (Succ c4)) bc3)
    -> (erased (List (Bool)) ts3 R4) (erased (RR ts3 R4) rr4) (erased (Bc ts3 c4) bc4)
    (erased (Reach p (MkTc 2 (DR) (bits "0111" L) R3) (MkTc 2 (DL) L (bits "1010" R4)) (BTrue)) rc))
  (let ((erased ts3) (erased w) (erased bc4)) (w-ex ts c4 bc3))
  (let ((erased R4) (erased rr4) (erased rc)) (r-inc p sg ts ts3 R3 (bits "111" L) w rr3))
  (values ts3 R4 rr4 bc4 (reach-catT p _ _ _ _ rc (so-d1 p sg L R4))))

(def-fns _ $ (erased do-reset : (erased (List (PT)) p) (erased (So34 p) sg) (subterm erased (Nat) v) (erased (List (Bool)) bs K ms R) (erased (Bool) a) (erased (Nat) c)
    (erased (PV bs v) pv) (erased (KR bs K) kr) (erased (RR ms R) rr) (erased (Bc ms c) bc) (erased (Lt v (Succ c)) le)
    -> (erased (List (Bool)) ms2 R2) (erased (RR ms2 R2) rr2)
    (erased (Reach p (MkTc 2 (DL) K (bits "101" (Cons (Bool) a R))) (MkTc 2 (DL) (Nil (Bool)) (bits "1010" R2)) (BTrue)) rc))
  (match erased (kr-split bs K v kr pv) _
    ((KS1 cs _ z lk bz)
      (let-match erased le (LtS _ _ l1))
      (let ((erased ts) (erased R3) (erased c4) (erased c2) (erased g) (erased rr3) (erased bc3) (erased ad) (erased le2) (erased rc1))
        (reset-pre p sg cs (bits "001") K ms R a z c lk bz rr bc (lt-weaken z c l1)))
      (let ((erased ts3) (erased R4) (erased rr4) (erased bc4) (erased rc3)) (reset-post p sg (Nil (Bool)) R3 ts c4 rr3 bc3))
      (values ts3 R4 rr4 (reach-cat2 p _ _ _ g rc1 (reach-catT p _ _ _ _ (so-k1 p sg (Nil (Bool)) R3) rc3))))
    ((KS2 cs _ bs2 K2 z w _ v2 lk bz kr2 pv2 azw lt)
      (let ((erased ts) (erased R3) (erased c4) (erased c2) (erased g) (erased rr3) (erased bc3) (erased ad) (erased le2) (erased rc1))
        (reset-pre p sg cs (bits "0010" K2) K ms R a z c lk bz rr bc (le-tr z v c (add-le-left z w v azw) le)))
      (let ((erased ts3) (erased R4) (erased rr4) (erased bc4) (erased rc3)) (reset-post p sg K2 R3 ts c4 rr3 bc3))
      (let ((erased lv)) (lt-le-trans v2 w v lt (add-le-left w z v (add-comm z w v azw))))
      (let ((erased lc)) (lt-le-trans v2 c2 (Succ c4) (lt-le-trans v2 w c2 lt (add-cancel-le z w v c2 c azw ad le)) (lt-weaken c2 (Succ c4) le2)))
      (let ((erased ms5) (erased R5) (erased rr5) (erased rc4)) (do-reset p sg (subterm (lt-subterm v2 v lv)) v2 bs2 K2 ts3 R4 (BFalse) c4 pv2 kr2 rr4 bc4 lc))
      (values ms5 R5 rr5 (reach-cat2 p _ _ _ g rc1 (reach-catT p _ _ _ _ (so-k0 p sg K2 R3) (reach-catT p _ _ _ _ rc3 rc4)))))))

(def-fns _ $ (erased so-step : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Bool)) ms R) (erased (RR ms R) rr)
    -> (erased (List (Bool)) ms2 R2) (erased (RR ms2 R2) rr2)
    (erased (Reach p (MkTc 2 (DL) (Nil (Bool)) (bits "1010" R)) (MkTc 2 (DL) (Nil (Bool)) (bits "1010" R2)) (BTrue)) rc))
  (let ((erased c) (erased bc)) (bc-ex ms))
  (let ((erased zs) (erased fz)) (fz-ex ms))
  (let ((erased n2) (erased v2) (erased X2) (erased ms2) (erased R2) (erased g) (erased nv2) (erased ad) (erased lr2) (erased rr2) (erased bc2) (erased fz2) (erased rc1))
    (d-run p sg c (N0) (Zero) (Nil (Bool)) ms R zs (NV0) (LnR0) rr bc fz))
  (let-match erased (add-fn c (Zero) v2 c ad (add-zero-right c)) (Refl _ _))
  (let ((erased n3) (erased X3) (erased nv3) (erased lr3) (erased rc2)) (l-inc p sg n2 v2 X2 (bits "1010" R2) nv2 lr2))
  (let-match erased nv3 (NVP bs3 _ pv3))
  (let-match erased lr3 (LnRP _ K3 kr3))
  (let ((erased zs2) (erased ov) (erased fz3)) (ov-ex ms2 bc2))
  (let-match erased (fz-fn ms2 zs zs2 fz2 fz3) (Refl _ _))
  (let ((erased R3) (erased rr3) (erased rc3)) (r-ov p sg ms2 (Cons (Bool) (BFalse) zs) R2 (bits "111" X3) ov rr2))
  (let ((erased z) (erased bz)) (bc-ex zs))
  (let ((erased dz) (erased adz)) (add-ex z z))
  (let ((erased le)) (LtS c (Succ dz) (le-tr c z dz (bc-fz ms zs c z fz bc bz) (add-le-left z z dz adz))))
  (let ((erased ms5) (erased R5) (erased rr5) (erased rc4))
    (do-reset p sg (Succ c) bs3 K3 (Cons (Bool) (BFalse) zs) R3 (BTrue) (Succ dz) pv3 kr3 rr3 (BcF zs z dz bz adz) le))
  (values ms5 R5 rr5 (reach-cat2 p _ _ _ g rc1 (reach-catT p _ _ _ _ rc2 (reach-catT p _ _ _ _ (so-d0 p sg X3 R2)
    (reach-catT p _ _ _ _ rc3 (reach-catT p _ _ _ _ (so-s0 p sg K3 R3) rc4)))))))

(def-adts
  ((SoI : ((Tc) e) -> Type)
    enum
    (many MkSoI : (erased (List (Bool)) ms R) (erased (RR ms R) rr) -> (SoI (MkTc 2 (DL) (Nil (Bool)) (bits "1010" R))))))

(def-fns _ $ (erased absurd so-loop : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Tr)) m) (erased (Ext p m) ex) (erased (Tc) e) (erased (SoI e) iv)
    (erased (Conf) c) (erased (AsC e c) ac) (subterm erased (Nat) u) (erased (HaltsAt m c u) hs) -> (erased (False) f))
  (let-match erased iv (MkSoI ms R rr))
  (let ((erased ms2) (erased R2) (erased rr2) (erased rc)) (so-step p sg ms R rr))
  (let ((erased c2) (erased ac2) (erased v) (erased hd) (erased lt)) (reach-halts p m ex _ _ c u rc ac hs))
  (so-loop p sg m ex _ (MkSoI ms2 R2 rr2) c2 ac2 (subterm (lt-subterm v u lt)) v hd))

(def-fns _ $ (erased absurd never-so : (erased (List (PT)) p) (erased (So34 p) sg) (erased (List (Tr)) m) (erased (Ext p m) ex)
    (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
  (let ((erased c0)) (MkAsC (Zero) (DR) _ _ _ _ _ _ _ (BFalse) (OrR _ (Nil (Bool)) (Nil (Bool))) (PullNil) (OrR _ (Nil (Bool)) (Nil (Bool)))))
  (let ((erased c2) (erased ac2) (erased v) (erased hd) (erased lt)) (reach-halts p m ex _ _ _ s (so-i0 p sg (Nil (Bool)) (Nil (Bool))) c0 hs))
  (so-loop p sg m ex _ (MkSoI (bits "1000010110") (bits "1110101010111011111011")
    (RRC _ _ _ (RRC _ _ _ (RRC _ _ _ (RRC _ _ _ (RRC _ _ _ (RRC _ _ _ (RRC _ _ _ (RRC _ _ _ (RRC _ _ _ (RRC _ _ _ (RRN)))))))))))) c2 ac2 v hd))

(let ((many p34)) (Cons _ (Def (Mov (BTrue) (DR) 1)) $ Cons _ (Def (Mov (BTrue) (DL) 2)) $ Cons _ (Def (Mov (BFalse) (DR) 2)) $ Cons _ (Def (Mov (BFalse) (DR) 1)) $
  Cons _ (Def (Mov (BTrue) (DL) 3)) $ Cons _ (Def (Mov (BFalse) (DL) 0)) $ Cons _ (Def (Mov (BTrue) (DL) 4)) $ Cons _ (Undef) $
  Cons _ (Def (Mov (BTrue) (DL) 0)) $ Cons _ (Def (Mov (BTrue) (DR) 0)) $ Nil (PT)))
(comptime-match many (so34-of p34) (ROk _ sg34))
(let ((many p35)) (Cons _ (Def (Mov (BTrue) (DR) 1)) $ Cons _ (Def (Mov (BTrue) (DL) 2)) $ Cons _ (Def (Mov (BFalse) (DR) 2)) $ Cons _ (Def (Mov (BFalse) (DR) 1)) $
  Cons _ (Def (Mov (BTrue) (DL) 3)) $ Cons _ (Def (Mov (BFalse) (DL) 0)) $ Cons _ (Def (Mov (BTrue) (DL) 4)) $ Cons _ (Undef) $
  Cons _ (Def (Mov (BTrue) (DL) 0)) $ Cons _ (Def (Mov (BFalse) (DL) 0)) $ Nil (PT)))
(comptime-match many (so34-of p35) (ROk _ sg35))

(def-adts
  ((SkOK : ((List (PT)) p) -> Type)
    enum
    (many SK10 : -> (SkOK p10))
    (many SK34 : -> (SkOK p34))
    (many SK35 : -> (SkOK p35))))

(def-fns _ $ (erased absurd never-sk : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (SkOK p) sk) (erased (Ext p m) ex)
    (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
  (match erased sk _
    (absurd (SK10) (never-sk10 m ex s hs))
    (absurd (SK34) (never-so p34 sg34 m ex s hs))
    (absurd (SK35) (never-so p35 sg35 m ex s hs))))

(def-fns _ $ (many check-sk : (many (List (PT)) p) -> (many (Res (SkOK p)) r))
  (let-match many (eq-pts p p10) (None _) ((Some _ e) (let-match erased e (Refl _ _)) (ROk _ (SK10))))
  (let-match many (eq-pts p p34) (None _) ((Some _ e) (let-match erased e (Refl _ _)) (ROk _ (SK34))))
  (let-match many (eq-pts p p35) (None _) ((Some _ e) (let-match erased e (Refl _ _)) (ROk _ (SK35))))
  (RFail _))
