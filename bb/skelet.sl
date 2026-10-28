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

(def-macro (sk-seg args here mw)
  (let ((many usage)) "`sk-seg` takes a name, a machine and two `(q d left-bits left-tail right-bits right-tail)` configurations")
  (let-match many args (Cons _ name r1) ((Nil _) (macro-fail mw here usage)))
  (let-match many r1 (Cons _ p r2) ((Nil _) (macro-fail mw here usage)))
  (let-match many r2 (Cons _ sa r3) ((Nil _) (macro-fail mw here usage)))
  (let-match many r3 (Cons _ sb _) ((Nil _) (macro-fail mw here usage)))
  (let ((unique mw1) (many lt)) (fresh-raw mw here "lt"))
  (let ((unique mw2) (many rt)) (fresh-raw mw1 here "rt"))
  (let ((unique mw3) (many g)) (fresh-raw mw2 here "g"))
  (let ((unique mw4) (many rr)) (fresh-raw mw3 here "r"))
  (let ((unique mw5) (many fa)) (sk-forms mw4 here sa lt rt))
  (let-match many fa (SkOk taa tca gta) ((SkBad) (macro-fail mw5 here usage)))
  (let ((unique mw6) (many fb)) (sk-forms mw5 here sb lt rt))
  (let-match many fb (SkOk tab tcb gtb) ((SkBad) (macro-fail mw6 here usage)))
  (values mw6 $ qq
    (comptime-match many (srun (~ p) (~ taa) (~ tab) 1000) (ROk _ (~ g)))
    (def-fns _ $ (erased (~ name) : (erased (List (Bool)) (~ lt) (~ rt)) -> (erased (Reach (~ p) (~ tca) (~ tcb) (BTrue)) (~ rr)))
      (arun-reach (~ p) _ _ (~ lt) (~ rt) _ _ (~ g) (~ gta) (~ gtb)))))

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

(sk-seg sk10-r0 p10 (1 DR "1" TV "" TZ) (3 DL "" TV "10" TZ))
(sk-seg sk10-r1 p10 (1 DR "1" TV "0" TV) (3 DL "" TV "10" TV))
(sk-seg sk10-r2 p10 (1 DR "1" TV "10" TV) (1 DR "111" TV "" TV))
(sk-seg sk10-r3 p10 (3 DL "11" TV "" TV) (3 DL "" TV "00" TV))
(sk-seg sk10-l0 p10 (3 DL "" TZ "11" TV) (0 DR "0101" TZ "" TV))
(sk-seg sk10-l1 p10 (3 DL "00" TV "11" TV) (0 DR "0101" TV "" TV))
(sk-seg sk10-l2 p10 (3 DL "0101" TV "11" TV) (3 DL "" TV "111111" TV))
(sk-seg sk10-l3 p10 (0 DR "" TV "1111" TV) (0 DR "0000" TV "" TV))
(sk-seg sk10-d0 p10 (3 DL "" TZ "10" TZ) (3 DL "01" TZ "010" TZ))
(sk-seg sk10-d1 p10 (3 DL "00" TV "10" TV) (1 DR "1101" TV "" TV))
(sk-seg sk10-d2 p10 (3 DL "101" TV "" TV) (3 DL "01" TV "0" TV))
(sk-seg sk10-d3 p10 (3 DL "0101" TV "00" TV) (3 DL "" TV "111100" TV))
(sk-seg sk10-d4 p10 (0 DR "" TV "1100" TV) (3 DL "00" TV "10" TV))
(sk-seg sk10-d5 p10 (3 DL "01" TV "0" TV) (3 DL "" TV "110" TV))
(sk-seg sk10-d6 p10 (0 DR "" TV "0" TV) (1 DR "1" TV "" TV))
(sk-seg sk10-i p10 ((Zero) DR "" TZ "" TZ) (3 DL "" TZ "10" TZ))

(def-fns _ $ (erased sk10-right : (erased (Dorf) n m) (erased (List (Bool)) l x) (subterm erased (ZR n x) z) (erased (Zi n m) zi) ->
    (erased (List (Bool)) y) (erased (ZR m y) z2) (erased (Reach p10 (MkTc 1 (DR) (Cons (Bool) (BTrue) l) x) (MkTc 3 (DL) l y) (BTrue)) rc))
  (match erased z _
    ((ZRE) (let-match erased zi (ZiE)) (values (bits "10") (ZRI _ _ (ZRE)) (sk10-r0 l x)))
    ((ZRO n1 x1 z1) (let-match erased zi (ZiO _)) (values (bits "10" x1) (ZRI _ _ z1) (sk10-r1 l x1)))
    ((ZRI n1 x1 z1)
      (let-match erased zi (ZiI _ m1 zi1))
      (let ((erased y1) (erased z2) (erased r2)) (sk10-right n1 m1 (bits "11" l) x1 z1 zi1))
      (values (bits "00" y1) (ZRO _ _ (ZRO _ _ z2)) (reach-catT p10 _ _ _ _ (sk10-r2 l x1) (reach-catT p10 _ _ _ _ r2 (sk10-r3 l y1)))))))

(def-fns _ $ (erased sk10-left : (erased (Dorf) n m) (erased (List (Bool)) x r) (subterm erased (TR n x) t) (erased (Zi n m) zi) ->
    (erased (List (Bool)) y) (erased (TR m y) t2) (erased (Reach p10 (MkTc 3 (DL) x (bits "11" r)) (MkTc 0 (DR) y r) (BTrue)) rc))
  (match erased t _
    ((TRE) (let-match erased zi (ZiE)) (values (bits "0101") (TRI _ _ (TRE)) (sk10-l0 x r)))
    ((TRO n1 x1 t1) (let-match erased zi (ZiO _)) (values (bits "0101" x1) (TRI _ _ t1) (sk10-l1 x1 r)))
    ((TRI n1 x1 t1)
      (let-match erased zi (ZiI _ m1 zi1))
      (let ((erased y1) (erased t2) (erased r2)) (sk10-left n1 m1 x1 (bits "1111" r) t1 zi1))
      (values (bits "0000" y1) (TRO _ _ (TRO _ _ t2)) (reach-catT p10 _ _ _ _ (sk10-l2 x1 r) (reach-catT p10 _ _ _ _ r2 (sk10-l3 y1 r)))))))

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
      (values (MkTc 3 (DL) (bits "01") (bits "010")) base (sk10-d0 l r)))
    ((LRO n0 x t)
      (let-match erased c (IncO _ _ zi))
      (match erased t _
        ((TRE)
          (let-match erased zi (ZiE))
          (let-match erased b (ZRI _ _ b1))
          (let-match erased b1 (ZRE))
          (values (MkTc 3 (DL) (bits "01") (bits "010")) base (sk10-d0 l r)))
        ((TRO n1 x1 t1)
          (let-match erased zi (ZiO _))
          (let-match erased b (ZRI _ r1 b1))
          (let ((erased m1) (erased zi1)) (zi-ex n1))
          (let ((erased y) (erased z2) (erased r2)) (sk10-right n1 m1 (bits "101" x1) r1 b1 zi1))
          (values (MkTc 3 (DL) (bits "01" x1) (bits "0" y)) (MkI10 (ZI n1) (ZO m1) _ _ (LRI _ _ t1) (ZRO _ _ z2) (IncI _ _ zi1))
            (reach-catT p10 _ _ _ _ (sk10-d1 x1 r1) (reach-catT p10 _ _ _ _ r2 (sk10-d2 x1 y)))))
        ((TRI n1 x1 t1)
          (let-match erased zi (ZiI _ m1 zi1))
          (let-match erased b (ZRO _ _ b1))
          (let-match erased b1 (ZRO _ r1 b2))
          (let ((erased y) (erased t2) (erased r2)) (sk10-left n1 m1 x1 (bits "1100" r1) t1 zi1))
          (values (MkTc 3 (DL) (bits "00" y) (bits "10" r1)) (MkI10 (ZO (ZO m1)) (ZI m1) _ _ (LRO _ _ (TRO _ _ t2)) (ZRI _ _ b2) (IncO _ _ (ZiO _)))
            (reach-catT p10 _ _ _ _ (sk10-d3 x1 r1) (reach-catT p10 _ _ _ _ r2 (sk10-d4 y r1)))))))
    ((LRI n0 x0 t)
      (let-match erased c (IncI _ m0 zi))
      (let-match erased b (ZRO _ r0 b0))
      (let ((erased y) (erased t2) (erased r2)) (sk10-left n0 m0 x0 (bits "0" r0) t zi))
      (let ((erased m2) (erased zi2)) (zi-ex m0))
      (let ((erased y2) (erased z3) (erased r4)) (sk10-right m0 m2 y r0 b0 zi2))
      (values (MkTc 3 (DL) y y2) (MkI10 (ZO m0) m2 _ _ (LRO _ _ t2) z3 (IncO _ _ zi2))
        (reach-catT p10 _ _ _ _ (sk10-d5 x0 r0) (reach-catT p10 _ _ _ _ r2 (reach-catT p10 _ _ _ _ (sk10-d6 y r0) r4)))))))

(def-fns _ $ (erased absurd sk10-loop : (erased (List (Tr)) m) (erased (Ext p10 m) ex) (erased (Tc) e) (erased (Inv10 e) iv) (erased (Conf) c) (erased (AsC e c) ac)
    (subterm erased (Nat) u) (erased (HaltsAt m c u) hs) -> (erased (False) f))
  (let ((erased e2) (erased iv2) (erased rc)) (sk10-step e iv))
  (let ((erased c2) (erased ac2) (erased v) (erased hd) (erased lt)) (reach-halts p10 m ex e e2 c u rc ac hs))
  (sk10-loop m ex e2 iv2 c2 ac2 (subterm (lt-subterm v u lt)) v hd))

(def-fns _ $ (erased absurd never-sk10 : (erased (List (Tr)) m) (erased (Ext p10 m) ex)
    (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
  (let ((erased c0)) (MkAsC (Zero) (DR) _ _ _ _ _ _ _ (BFalse) (OrR _ (Nil (Bool)) (Nil (Bool))) (PullNil) (OrR _ (Nil (Bool)) (Nil (Bool)))))
  (let ((erased c2) (erased ac2) (erased v) (erased hd) (erased lt)) (reach-halts p10 m ex _ _ _ s (sk10-i (Nil (Bool)) (Nil (Bool))) c0 hs))
  (sk10-loop m ex _ (MkI10 (ZE) (ZI (ZE)) _ _ (LRE) (ZRI _ _ (ZRE)) (IncE)) c2 ac2 v hd))

(def-adts
  ((SkOK : ((List (PT)) p) -> Type)
    enum
    (many SK10 : -> (SkOK p10))))

(def-fns _ $ (erased absurd never-sk : (erased (List (PT)) p) (erased (List (Tr)) m) (erased (SkOK p) sk) (erased (Ext p m) ex)
    (erased (Nat) s) (erased (HaltsAt m (MkConf (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hs) -> (erased (False) f))
  (match erased sk _
    (absurd (SK10) (never-sk10 m ex s hs))))

(def-fns _ $ (many check-sk : (many (List (PT)) p) -> (many (Res (SkOK p)) r))
  (let-match many (eq-pts p p10) (Some _ e) ((None _) (RFail _)))
  (let-match erased e (Refl _ _))
  (ROk _ (SK10)))
