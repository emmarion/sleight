; The completeness half of ctree_mem_cpcolor of cfcolor.v: the tree cpcolor-c computes for a cubic program holds the even
; normal form of every ring trace of a colouring of the program's map. Load after red/ccheck.sl.

; et2 is et after the cubic step s, as a ring trace of the map before s becomes one of the map after it (cpcolor1 of
; cfcolor.v, read as a relation).
(def-adts $ (StepTr : ((Step) s) ((List (Col)) et et2) -> Type)
  enum
  (many STR : (erased (Nat) k) (erased (List (Col)) et et2) (erased (Rot (Col) k et et2) rt) -> (StepTr (SR k) et et2))
  (many STU : (erased (Col) c) (erased (List (Col)) et) (erased (NZ c) nz) -> (StepTr (SU) et (Cons (Col) c (Cons (Col) c et))))
  (many STY : (erased (Col) e1 g h) (erased (List (Col)) r1) (erased (AddC e1 g h) p) (erased (NZ g) ng) (erased (NZ h) nh)
      -> (StepTr (SY) (Cons (Col) e1 r1) (Cons (Col) g (Cons (Col) h r1))))
  (many STH : (erased (Col) e1 e2 ee g s1 h) (erased (List (Col)) r2) (erased (AddC e1 e2 ee) pee) (erased (AddC e1 g s1) ps1) (erased (AddC ee g h) ph)
      (erased (NZ g) ng) (erased (NZ s1) ns1) (erased (NZ h) nh) -> (StepTr (SH) (Cons (Col) e1 (Cons (Col) e2 r2)) (Cons (Col) g (Cons (Col) h r2)))))

; Running the steps cp1, in application order, from et can give et2.
(def-adts $ (StepsTr : ((List (Step)) cp1) ((List (Col)) et et2) -> Type)
  enum
  (many SNil : (erased (List (Col)) et) -> (StepsTr (Nil (Step)) et et))
  (many SCons : (erased (Step) s) (erased (List (Step)) cp1) (erased (List (Col)) et et1 et2) (erased (StepTr s et et1) st) (erased (StepsTr cp1 et1 et2) rest)
      -> (StepsTr (Cons (Step) s cp1) et et2)))

(def-fns _ $ (erased or-sel : (erased (Ctree) tl tr l r) (erased (Col) e) (erased (List (Col)) w) (erased (Or (CtMem tl (Cons (Col) e w)) (CtMem tr (Cons (Col) e w))) m)
    (erased (CtSel tl e l) sl) (erased (CtSel tr e r) sr) -> (erased (Or (CtMem l w) (CtMem r w)) res))
  (match erased m _ ((InL _ _ ma) (InL _ _ (mem-sel tl l e w ma sl))) ((InR _ _ ma) (InR _ _ (mem-sel tr r e w ma sr)))))

(def-fns _ $ (erased or-in : (erased (Ctree) tl tr t) (subterm erased (List (Col)) w) (subterm erased (CtOr tl tr t) o) (erased (Or (CtMem tl w) (CtMem tr w)) m)
    -> (erased (CtMem t w) r))
  (match erased o _
    ((OrEL _) (match erased m _ (absurd (InL _ _ m1) (mem-empty w m1)) ((InR _ _ m1) m1)))
    ((OrER _) (match erased m _ ((InL _ _ m1) m1) (absurd (InR _ _ m1) (mem-empty w m1))))
    ((OrLL a b)
      (let-match erased (match erased m (((Eq (List (Col)) w (Nil (Col))) q))
        ((InL _ _ m1) (leaf-mem-nil a w m1)) ((InR _ _ m1) (leaf-mem-nil b w m1))) (Refl _ _))
      (leaf-mem (CEmpty)))
    ((OrNN l1 l2 l3 r1 r2 r3 u1 u2 u3 _ o1 o2 o3 c)
      (let-match erased w (Cons _ e w1)
        (absurd (Nil _) (match erased m _
          (absurd (InL _ _ m1) (let-match erased m1 (MkCtMem _ _ n p)) (let-match erased p (SubNil _ _ rt)) rt)
          (absurd (InR _ _ m1) (let-match erased m1 (MkCtMem _ _ n p)) (let-match erased p (SubNil _ _ rt)) rt))))
      (match erased e _
        ((C0) (match erased (or-sel tl tr (CEmpty) (CEmpty) e w1 m (SelN0 l1 l2 l3) (SelN0 r1 r2 r3)) _
          (absurd (InL _ _ m1) (mem-empty w1 m1)) (absurd (InR _ _ m1) (mem-empty w1 m1))))
        ((C1) (mem-cons t u1 e w1 (cons-sel-back u1 u2 u3 t u1 e c (SelN1 u1 u2 u3))
          (or-in l1 r1 u1 w1 o1 (or-sel tl tr l1 r1 e w1 m (SelN1 l1 l2 l3) (SelN1 r1 r2 r3)))))
        ((C2) (mem-cons t u2 e w1 (cons-sel-back u1 u2 u3 t u2 e c (SelN2 u1 u2 u3))
          (or-in l2 r2 u2 w1 o2 (or-sel tl tr l2 r2 e w1 m (SelN2 l1 l2 l3) (SelN2 r1 r2 r3)))))
        ((C3) (mem-cons t u3 e w1 (cons-sel-back u1 u2 u3 t u3 e c (SelN3 u1 u2 u3))
          (or-in l3 r3 u3 w1 o3 (or-sel tl tr l3 r3 e w1 m (SelN3 l1 l2 l3) (SelN3 r1 r2 r3)))))))))

(def-fns _ $ (erased nmem-or : (erased (Ctree) tl tr t) (erased (List (Col)) l) (erased (CtOr tl tr t) o) (erased (Or (NMem tl l) (NMem tr l)) b)
    -> (erased (NMem t l) r))
  (match erased b _
    ((InL _ _ x) (match erased x _ ((NMZ _ _ z) (NMZ t l z)) ((NMIn _ _ p n m) (NMIn t l p n (or-in tl tr t p o (InL _ _ m))))))
    ((InR _ _ x) (match erased x _ ((NMZ _ _ z) (NMZ t l z)) ((NMIn _ _ p n m) (NMIn t l p n (or-in tl tr t p o (InR _ _ m))))))))

(def-fns _ $ (erased brmem-or : (erased (Ctree) tl tr t) (erased (List (Col)) et) (erased (CtOr tl tr t) o) (erased (Or (BrMem et tl) (BrMem et tr)) b)
    -> (erased (BrMem et t) r))
  (match erased b _
    ((InL _ _ x) (let-match erased x (MkBrMem e0 e1 rest grest _ g ip pg pt nm))
      (MkBrMem e0 e1 rest grest t g ip pg pt (nmem-or tl tr t grest o (InL _ _ nm))))
    ((InR _ _ x) (let-match erased x (MkBrMem e0 e1 rest grest _ g ip pg pt nm))
      (MkBrMem e0 e1 rest grest t g ip pg pt (nmem-or tl tr t grest o (InR _ _ nm))))))

(def-fns _ $ (erased allnz-snoc : (erased (List (Col)) xs ys) (erased (Col) x) (subterm erased (Snoc (Col) xs x ys) s) (erased (AllNZ xs) a) (erased (NZ x) nx)
    -> (erased (AllNZ ys) r))
  (match erased s _
    ((SnocNil _ _) (AllNZCons x (Nil (Col)) nx (AllNZNil)))
    ((SnocCons _ y _ xs1 ys1 s1) (let-match erased a (AllNZCons _ _ ny a1)) (AllNZCons y ys1 ny (allnz-snoc xs1 ys1 x s1 a1 nx)))))

(def-fns _ $ (erased allnz-rots : (erased (Nat) k) (erased (List (Col)) xs ys) (subterm erased (Rots (Col) k xs ys) rs) (erased (AllNZ xs) a) -> (erased (AllNZ ys) r))
  (let-match erased rs (RotsS _ k1 x xs1 xs2 _ s rs1) ((RotsZ _ _) a))
  (let-match erased a (AllNZCons _ _ nx a1))
  (allnz-rots k1 xs2 ys rs1 (allnz-snoc xs1 xs2 x s a1 nx)))

(def-fns _ $ (erased allnz-rot : (erased (Nat) k) (erased (List (Col)) xs ys) (erased (Rot (Col) k xs ys) rt) (erased (AllNZ xs) a) -> (erased (AllNZ ys) r))
  (match erased rt _ ((RotIn _ _ _ _ _ _ _ rs) (allnz-rots k xs ys rs a)) ((RotOver _ _ _ _ _ _) a)))

(def-fns _ $ (erased addc-eq : (erased (Col) a b c d) (erased (AddC a b c) p) (erased (AddC a b d) q) -> (erased (Eq (Col) c d) e))
  (addc-fn a b c d (addc-k a b c p) (addc-k a b d q)))

(def-fns _ $ (erased third-of : (erased (Col) a b c) (erased (AddC a b c) p) (erased (NZ a) na) (erased (NZ b) nb) (erased (NZ c) nc) -> (erased (Third a b c) t))
  (match erased (addc-k a b c p) _ (absurd (AZL _) na) (absurd (AZR _) nb) (absurd (ASame _) nc) ((AThird _ _ _ t) t)))

; b2 c2 is b c or c b.
(def-adts $ (Pick2 : ((Col) b2 c2 b c) -> Type)
  enum
  (many PkSame : (erased (Col) b c) -> (Pick2 b c b c))
  (many PkSwap : (erased (Col) b c) -> (Pick2 c b b c)))

(def-fns _ $ (erased third-pick : (erased (Col) a b c b2 c2) (erased (Third a b c) p) (erased (Third a b2 c2) q) -> (erased (Pick2 b2 c2 b c) r))
  (match erased p _
    ((T123) (match erased q _ ((T123) (PkSame b c)) ((T132) (PkSwap b c))))
    ((T132) (match erased q _ ((T132) (PkSame b c)) ((T123) (PkSwap b c))))
    ((T213) (match erased q _ ((T213) (PkSame b c)) ((T231) (PkSwap b c))))
    ((T231) (match erased q _ ((T231) (PkSame b c)) ((T213) (PkSwap b c))))
    ((T312) (match erased q _ ((T312) (PkSame b c)) ((T321) (PkSwap b c))))
    ((T321) (match erased q _ ((T321) (PkSame b c)) ((T312) (PkSwap b c))))))

(def-fns _ $ (erased absurd notr-refute : (erased (Step) s) (erased (List (Col)) et et2) (erased (NotTr s et) nt) (erased (StepTr s et et2) st) -> (erased (False) f))
  (match erased nt _
    (absurd (NTRr _) st)
    (absurd (NTK _) st)
    (absurd (NTY) st)
    (absurd (NTH _ sh) (let-match erased st (STH _ _ _ _ _ _ _ _ _ _ _ _ _)) sh)))

(def-fns _ $ (erased allnz2 : (erased (Col) g h) (erased (List (Col)) r) (erased (NZ g) ng) (erased (NZ h) nh) (erased (AllNZ r) a)
    -> (erased (AllNZ (Cons (Col) g (Cons (Col) h r))) res))
  (AllNZCons g (Cons (Col) h r) ng (AllNZCons h r nh a)))

; Every trace that the steps cp1 can give from et has its normalisation in t.
(def-fns _ $ (erased cov-mem : (erased (List (Step)) cp1) (erased (List (Col)) et et2) (erased (Ctree) t) (subterm erased (Cov cp1 et t) cv)
    (erased (StepsTr cp1 et et2) st) (erased (AllNZ et) nz) -> (erased (BrMem et2 t) r))
  (match erased cv _
    ((CvNil _ _ bm) (let-match erased st (SNil _)) bm)
    (absurd (CvVoid s cp2 _ _ nt) (let-match erased st (SCons _ _ _ et1 _ s1 _)) (notr-refute s et et1 nt s1))
    ((CvR k cp2 _ et3 _ rt c)
      (let-match erased st (SCons _ _ _ et1 _ s1 st1))
      (let-match erased s1 (STR _ _ _ rt1))
      (let-match erased (rot-fn (Col) k et et1 et3 rt1 rt) (Refl _ _))
      (cov-mem cp2 et1 et2 t c st1 (allnz-rot k et et1 rt nz)))
    ((CvU cp2 _ t1 t2 t3 u _ ou o c1 c2 c3)
      (let-match erased st (SCons _ _ _ et1 _ s1 st1))
      (let-match erased s1 (STU c _ nzc))
      (let ((erased a)) (allnz2 c c et nzc nzc nz))
      (match erased nzc _
        ((NZ1) (brmem-or t1 u t et2 o (InL _ _ (cov-mem cp2 et1 et2 t1 c1 st1 a))))
        ((NZ2) (brmem-or t1 u t et2 o (InR _ _ (brmem-or t2 t3 u et2 ou (InL _ _ (cov-mem cp2 et1 et2 t2 c2 st1 a))))))
        ((NZ3) (brmem-or t1 u t et2 o (InR _ _ (brmem-or t2 t3 u et2 ou (InR _ _ (cov-mem cp2 et1 et2 t3 c3 st1 a))))))))
    ((CvY e1 e2 e3 r1 cp2 t1 t2 _ p2 p3 c1 c2 o)
      (let-match erased st (SCons _ _ _ et1 _ s1 st1))
      (let-match erased s1 (STY _ g h _ pa ng nh))
      (let-match erased nz (AllNZCons _ _ nz1 nzr))
      (let ((erased a23) (erased a32) (erased n2) (erased n3)) (others e1 e2 e3 nz1 p2 p3))
      (let ((erased a)) (allnz2 g h r1 ng nh nzr))
      (match erased (third-pick e1 e2 e3 g h (third-of e1 e2 e3 a23 nz1 n2 n3) (third-of e1 g h pa nz1 ng nh)) _
        ((PkSame _ _) (brmem-or t1 t2 t et2 o (InL _ _ (cov-mem cp2 et1 et2 t1 c1 st1 a))))
        ((PkSwap _ _) (brmem-or t1 t2 t et2 o (InR _ _ (cov-mem cp2 et1 et2 t2 c2 st1 a))))))
    ((CvH0 e1 e2 g1 g2 r2 cp2 t1 t2 _ p p2 p3 c1 c2 o)
      (let-match erased st (SCons _ _ _ et1 _ s1 st1))
      (let-match erased s1 (STH _ _ ee g s h _ pee ps ph ng ns nh))
      (let-match erased nz (AllNZCons _ _ nz1 nzr))
      (let-match erased nzr (AllNZCons _ _ _ nzr2))
      (let-match erased (addc-eq e1 e2 ee (C0) pee p) (Refl _ _))
      (let-match erased (addc-eq (C0) g h g ph (addc-0l g)) (Refl _ _))
      (let ((erased a23) (erased a32) (erased n2) (erased n3)) (others e1 g1 g2 nz1 p2 p3))
      (let ((erased a)) (allnz2 g g r2 ng ng nzr2))
      (match erased (third-pick e1 g1 g2 g s (third-of e1 g1 g2 a23 nz1 n2 n3) (third-of e1 g s ps nz1 ng ns)) _
        ((PkSame _ _) (brmem-or t1 t2 t et2 o (InL _ _ (cov-mem cp2 et1 et2 t1 c1 st1 a))))
        ((PkSwap _ _) (brmem-or t1 t2 t et2 o (InR _ _ (cov-mem cp2 et1 et2 t2 c2 st1 a))))))
    ((CvH e1 e2 sm r2 cp2 _ p nzs c)
      (let-match erased st (SCons _ _ _ et1 _ s1 st1))
      (let-match erased s1 (STH _ _ ee g s h _ pee ps ph ng ns nh))
      (let-match erased nz (AllNZCons _ _ nz1 nzr))
      (let-match erased nzr (AllNZCons _ _ nz2 nzr2))
      (let-match erased (addc-eq e1 e2 ee sm pee p) (Refl _ _))
      (match erased (third-pick e1 e2 sm g s (third-of e1 e2 sm p nz1 nz2 nzs) (third-of e1 g s ps nz1 ng ns)) _
        ((PkSame _ _)
          (let-match erased (addc-eq sm e2 h e1 ph (addc-comm e2 sm e1 (addc-cancel e2 sm e1 (addc-comm e1 e2 sm p)))) (Refl _ _))
          (cov-mem cp2 et1 et2 t c st1 (allnz2 e2 e1 r2 nz2 nz1 nzr2)))
        (absurd (PkSwap _ _) (addc-self sm h ph nh))))))

(def-fns _ $ (erased third-nz : (erased (Col) a b c) (erased (Third a b c) t) -> (erased (NZ a) na) (erased (NZ b) nb) (erased (NZ c) nc))
  (match erased t _
    ((T123) (values (NZ1) (NZ2) (NZ3))) ((T132) (values (NZ1) (NZ3) (NZ2))) ((T213) (values (NZ2) (NZ1) (NZ3)))
    ((T231) (values (NZ2) (NZ3) (NZ1))) ((T312) (values (NZ3) (NZ1) (NZ2))) ((T321) (values (NZ3) (NZ2) (NZ1)))))

(def-fns _ $ (erased third-isperm : (erased (Col) a b c) (erased (Third a b c) t) -> (erased (IsPerm (MkPerm a b c)) ip))
  (match erased t _ ((T123) (IP123)) ((T132) (IP132)) ((T213) (IP213)) ((T231) (IP231)) ((T312) (IP312)) ((T321) (IP321))))

(def-fns _ $ (erased nz-perm : (erased (Perm) g) (erased (Col) c d) (erased (IsPerm g) ip) (erased (PermC g c d) pc) (erased (NZ c) nz) -> (erased (NZ d) r))
  (let-match erased g (MkPerm p1 p2 p3))
  (let ((erased n1) (erased n2) (erased n3)) (third-nz p1 p2 p3 (perm-third p1 p2 p3 ip)))
  (match erased pc _ (absurd (PC0 _) nz) ((PC1 _ _ _) n1) ((PC2 _ _ _) n2) ((PC3 _ _ _) n3)))

(def-fns _ $ (erased allnz-perm : (erased (Perm) g) (erased (List (Col)) l l2) (erased (IsPerm g) ip) (subterm erased (PermT g l l2) pt) (erased (AllNZ l) a)
    -> (erased (AllNZ l2) r))
  (let-match erased pt (PTCons _ c d l1 l3 pc pt1) ((PTNil _) (AllNZNil)))
  (let-match erased a (AllNZCons _ _ nc a1))
  (AllNZCons d l3 (nz-perm g c d ip pc nc) (allnz-perm g l1 l3 ip pt1 a1)))

(def-fns _ $ (erased absurd allnz-hasc0 : (erased (List (Col)) l) (subterm erased (AllNZ l) a) (erased (HasC0 l) z) -> (erased (False) f))
  (let-match erased a (AllNZCons c l1 nc a1) (absurd (AllNZNil) z))
  (match erased z _ (absurd (HZHere _) nc) (absurd (HZThere _ _ z1) (allnz-hasc0 l1 a1 z1))))

(def-fns _ $ (erased permt-up : (erased (Perm) g) (erased (List (Col)) xs xs2 pxs) (erased (Col) x px) (subterm erased (Snoc (Col) xs x xs2) s)
    (erased (PermT g xs pxs) pt) (erased (PermC g x px) pc) -> (erased (List (Col)) pxs2) (erased (Snoc (Col) pxs px pxs2) ps) (erased (PermT g xs2 pxs2) pt2))
  (match erased s _
    ((SnocNil _ _) (let-match erased pt (PTNil _)) (values (Cons _ px (Nil _)) (SnocNil _ px) (PTCons g x px _ _ pc (PTNil g))))
    ((SnocCons _ y _ xs1 ys1 s1)
      (let-match erased pt (PTCons _ _ py _ pxs1 pcy pt1))
      (let ((erased pys) (erased ps) (erased pt2)) (permt-up g xs1 ys1 pxs1 x px s1 pt1 pc))
      (values (Cons _ py pys) (SnocCons _ py px pxs1 pys ps) (PTCons g y py ys1 pys pcy pt2)))))

(def-fns _ $ (erased rots-perm : (erased (Perm) g) (erased (Nat) k) (erased (List (Col)) xs ys pxs) (subterm erased (Rots (Col) k xs ys) rs) (erased (PermT g xs pxs) pt)
    -> (erased (List (Col)) pys) (erased (Rots (Col) k pxs pys) prs) (erased (PermT g ys pys) pt2))
  (let-match erased rs (RotsS _ k1 x xs1 xs2 _ s rs1) ((RotsZ _ _) (values pxs (RotsZ _ pxs) pt)))
  (let-match erased pt (PTCons _ _ px _ pxs1 pc pt1))
  (let ((erased pxs2) (erased ps) (erased ptx)) (permt-up g xs1 xs2 pxs1 x px s pt1 pc))
  (let ((erased pys) (erased prs) (erased pt2)) (rots-perm g k1 xs2 ys pxs2 rs1 ptx))
  (values pys (RotsS _ k1 px pxs1 pxs2 pys ps prs) pt2))

(def-fns _ $ (erased rot-perm : (erased (Perm) g) (erased (Nat) k) (erased (List (Col)) xs ys pxs) (erased (Rot (Col) k xs ys) rt) (erased (PermT g xs pxs) pt)
    -> (erased (List (Col)) pys) (erased (Rot (Col) k pxs pys) prt) (erased (PermT g ys pys) pt2))
  (match erased rt _
    ((RotIn _ _ m _ _ l le rs)
      (let ((erased pys) (erased prs) (erased pt2)) (rots-perm g k xs ys pxs rs pt))
      (values pys (RotIn _ k m pxs pys (permt-length g xs pxs m pt l) le prs) pt2))
    ((RotOver _ _ m _ l gt) (values pxs (RotOver _ k m pxs (permt-length g xs pxs m pt l) gt) pt))))

; A colour permutation of a run of steps is a run of steps.
(def-fns _ $ (erased step-perm : (erased (Perm) g) (erased (Step) s) (erased (List (Col)) et et1 pet) (erased (IsPerm g) ip) (erased (StepTr s et et1) st)
    (erased (PermT g et pet) pt) -> (erased (List (Col)) pet1) (erased (StepTr s pet pet1) pst) (erased (PermT g et1 pet1) pt1))
  (match erased st _
    ((STR k _ _ rt) (let ((erased py) (erased prt) (erased pt2)) (rot-perm g k et et1 pet rt pt)) (values py (STR k pet py prt) pt2))
    ((STU c _ nz)
      (let ((erased d) (erased pc)) (permc-ex g c ip))
      (values (Cons _ d (Cons _ d pet)) (STU d pet (nz-perm g c d ip pc nz)) (PTCons g c d _ _ pc (PTCons g c d et pet pc pt))))
    ((STY e1 a b r1 p na nb)
      (let-match erased pt (PTCons _ _ d1 _ pr1 pc1 ptr))
      (let ((erased da) (erased pa)) (permc-ex g a ip))
      (let ((erased db) (erased pb)) (permc-ex g b ip))
      (values (Cons _ da (Cons _ db pr1)) (STY d1 da db pr1 (permc-add g e1 a b d1 da db ip p pc1 pa pb) (nz-perm g a da ip pa na) (nz-perm g b db ip pb nb))
        (PTCons g a da _ _ pa (PTCons g b db r1 pr1 pb ptr))))
    ((STH e1 e2 ee a s1 b r2 pee ps1 ph na ns nb)
      (let-match erased pt (PTCons _ _ d1 _ pr pc1 ptr))
      (let-match erased ptr (PTCons _ _ d2 _ pr2 pc2 ptr2))
      (let ((erased dee) (erased pdee)) (permc-ex g ee ip))
      (let ((erased da) (erased pa)) (permc-ex g a ip))
      (let ((erased ds) (erased pds)) (permc-ex g s1 ip))
      (let ((erased db) (erased pb)) (permc-ex g b ip))
      (values (Cons _ da (Cons _ db pr2))
        (STH d1 d2 dee da ds db pr2 (permc-add g e1 e2 ee d1 d2 dee ip pee pc1 pc2 pdee) (permc-add g e1 a s1 d1 da ds ip ps1 pc1 pa pds)
          (permc-add g ee a b dee da db ip ph pdee pa pb) (nz-perm g a da ip pa na) (nz-perm g s1 ds ip pds ns) (nz-perm g b db ip pb nb))
        (PTCons g a da _ _ pa (PTCons g b db r2 pr2 pb ptr2))))))

(def-fns _ $ (erased steps-perm : (erased (Perm) g) (erased (List (Step)) cp1) (erased (List (Col)) et et2 pet) (erased (IsPerm g) ip)
    (subterm erased (StepsTr cp1 et et2) st) (erased (PermT g et pet) pt) -> (erased (List (Col)) pet2) (erased (StepsTr cp1 pet pet2) pst) (erased (PermT g et2 pet2) pt2))
  (match erased st _
    ((SNil _) (values pet (SNil pet) pt))
    ((SCons s cp2 _ et1 _ s1 st1)
      (let ((erased pet1) (erased ps1) (erased pt1)) (step-perm g s et et1 pet ip s1 pt))
      (let ((erased pet2) (erased pst) (erased pt2)) (steps-perm g cp2 et1 et2 pet1 ip st1 pt1))
      (values pet2 (SCons s cp2 pet pet1 pet2 ps1 pst) pt2))))

(def-fns _ $ (erased erot-ex : (erased (Col) c) (erased (NZ c) nz) -> (erased (Perm) g) (erased (IsPerm g) ip) (erased (PermC g c (C1)) p))
  (match erased nz _
    ((NZ1) (values p123 (IP123) (PC1 (C1) (C2) (C3))))
    ((NZ2) (values p312 (IP312) (PC2 (C3) (C1) (C2))))
    ((NZ3) (values p231 (IP231) (PC3 (C2) (C3) (C1))))))

; The permutation sending a b c to 1 2 3.
(def-fns _ $ (erased third-inv : (erased (Col) a b c) (erased (Third a b c) t) -> (erased (Perm) g) (erased (IsPerm g) ip) (erased (PermC g a (C1)) pa)
    (erased (PermC g b (C2)) pb) (erased (PermC g c (C3)) pc))
  (let ((erased g) (erased pi) (erased ip)) (perminv-ex (MkPerm a b c) (third-isperm a b c t)))
  (values g ip (permc-invert (MkPerm a b c) g (C1) a pi (PC1 a b c)) (permc-invert (MkPerm a b c) g (C2) b pi (PC2 a b c))
    (permc-invert (MkPerm a b c) g (C3) c pi (PC3 a b c))))

; Up to a colour permutation, every trace that the steps cp1 can give from c c has its normalisation in t.
(def-fns _ $ (erased cov0-mem : (erased (List (Step)) cp1) (erased (Col) c) (erased (List (Col)) et2) (erased (Ctree) t) (subterm erased (Cov0 cp1 t) cv)
    (erased (StepsTr cp1 (Cons (Col) c (Cons (Col) c (Nil (Col)))) et2) st) (erased (NZ c) nz)
    -> (erased (Perm) g) (erased (IsPerm g) ip) (erased (List (Col)) pet) (erased (PermT g et2 pet) pt) (erased (BrMem pet t) bm))
  (let ((erased cc2) (erased nil)) (values (Cons (Col) c (Cons (Col) c (Nil (Col)))) (Nil (Col))))
  (let ((erased n1) (erased n11)) (values (AllNZCons (C1) nil (NZ1) (AllNZNil)) (allnz2 (C1) (C1) nil (NZ1) (NZ1) (AllNZNil))))
  (match erased cv _
    ((C0Base _ _ c0)
      (let ((erased g) (erased ip) (erased pg)) (erot-ex c nz))
      (let ((erased pet) (erased pst) (erased pt)) (steps-perm g cp1 cc2 et2 c11 ip st (PTCons g c (C1) _ _ pg (PTCons g c (C1) nil nil pg (PTNil g)))))
      (values g ip pet pt (cov-mem cp1 c11 pet t c0 pst n11)))
    ((C0R k cp2 _ c0)
      (let-match erased st (SCons _ _ _ et1 _ s1 st1))
      (let-match erased s1 (STR _ _ _ rt))
      (let-match erased (rot-fn (Col) k cc2 et1 cc2 rt (rot-cc c k)) (Refl _ _))
      (cov0-mem cp2 c et2 t c0 st1 nz))
    ((C0Y cp2 _ c0)
      (let-match erased st (SCons _ _ _ et1 _ s1 st1))
      (let-match erased s1 (STY _ a b _ pab na nb))
      (let ((erased g) (erased ip) (erased pa) (erased pb) (erased pc)) (third-inv a b c (third-23 a c b (third-12 c a b (third-of c a b pab nz na nb)))))
      (let ((erased pet) (erased pst) (erased pt)) (steps-perm g cp2 et1 et2 _ ip st1 (PTCons g a (C1) _ _ pa (PTCons g b (C2) _ _ pb (PTCons g c (C3) _ _ pc (PTNil g))))))
      (values g ip pet pt (cov-mem cp2 _ pet t c0 pst (allnz2 (C1) (C2) (Cons (Col) (C3) nil) (NZ1) (NZ2) (AllNZCons (C3) nil (NZ3) (AllNZNil))))))
    ((C0U cp2 t1 t2 _ c1 c2 o)
      (let-match erased st (SCons _ _ _ et1 _ s1 st1))
      (let-match erased s1 (STU a _ na))
      (let ((erased x) (erased pax)) (addc-total a c))
      (match erased pax _
        (absurd (AZL _) na)
        (absurd (AZR _) nz)
        ((ASame _)
          (let ((erased g) (erased ip) (erased pg)) (erot-ex c nz))
          (let ((erased pet) (erased pst) (erased pt)) (steps-perm g cp2 et1 et2 _ ip st1
            (PTCons g c (C1) _ _ pg (PTCons g c (C1) _ _ pg (PTCons g c (C1) _ _ pg (PTCons g c (C1) _ _ pg (PTNil g)))))))
          (values g ip pet pt (brmem-or t1 t2 t pet o (InR _ _ (cov-mem cp2 _ pet t2 c2 pst (allnz2 (C1) (C1) _ (NZ1) (NZ1) n11))))))
        ((AThird _ _ _ th)
          (let ((erased g) (erased ip) (erased pa) (erased pb) (erased _)) (third-inv a c x th))
          (let ((erased pet) (erased pst) (erased pt)) (steps-perm g cp2 et1 et2 _ ip st1
            (PTCons g a (C1) _ _ pa (PTCons g a (C1) _ _ pa (PTCons g c (C2) _ _ pb (PTCons g c (C2) _ _ pb (PTNil g)))))))
          (values g ip pet pt (brmem-or t1 t2 t pet o (InL _ _ (cov-mem cp2 _ pet t1 c1 pst
            (allnz2 (C1) (C1) _ (NZ1) (NZ1) (allnz2 (C2) (C2) nil (NZ2) (NZ2) (AllNZNil))))))))))))

; c is b after a.
(def-adts $ (PComp : ((Perm) a b c) -> Type)
  enum
  (many MkPComp : (erased (Col) a1 a2 a3 c1 c2 c3) (erased (Perm) b) (erased (PermC b a1 c1) p1) (erased (PermC b a2 c2) p2) (erased (PermC b a3 c3) p3)
      -> (PComp (MkPerm a1 a2 a3) b (MkPerm c1 c2 c3))))

(def-fns _ $ (erased pcomp-ex : (erased (Perm) a b) (erased (IsPerm a) ia) (erased (IsPerm b) ib) -> (erased (Perm) c) (erased (PComp a b c) pc) (erased (IsPerm c) ic))
  (let-match erased a (MkPerm a1 a2 a3))
  (let ((erased c1) (erased p1)) (permc-ex b a1 ib))
  (let ((erased c2) (erased p2)) (permc-ex b a2 ib))
  (let ((erased c3) (erased p3)) (permc-ex b a3 ib))
  (values (MkPerm c1 c2 c3) (MkPComp a1 a2 a3 c1 c2 c3 b p1 p2 p3)
    (third-isperm c1 c2 c3 (third-perm b a1 a2 a3 c1 c2 c3 ib (perm-third a1 a2 a3 ia) p1 p2 p3))))

(def-fns _ $ (erased pcomp-c : (erased (Perm) a b c) (erased (Col) x y z) (erased (PComp a b c) pc) (erased (PermC a x y) pa) (erased (PermC b y z) pb)
    -> (erased (PermC c x z) r))
  (let-match erased pc (MkPComp a1 a2 a3 c1 c2 c3 _ q1 q2 q3))
  (match erased pa _
    ((PC0 _) (let-match erased pb (PC0 _)) (PC0 c))
    ((PC1 _ _ _) (let-match erased (permc-fn b a1 z c1 pb q1) (Refl _ _)) (PC1 c1 c2 c3))
    ((PC2 _ _ _) (let-match erased (permc-fn b a2 z c2 pb q2) (Refl _ _)) (PC2 c1 c2 c3))
    ((PC3 _ _ _) (let-match erased (permc-fn b a3 z c3 pb q3) (Refl _ _)) (PC3 c1 c2 c3))))

(def-fns _ $ (erased permt-comp : (erased (Perm) a b c) (erased (List (Col)) l l1 l2) (erased (PComp a b c) pc) (subterm erased (PermT a l l1) p) (erased (PermT b l1 l2) q)
    -> (erased (PermT c l l2) r))
  (let-match erased p (PTCons _ x y lr l1r px p1) ((PTNil _) (let-match erased q (PTNil _)) (PTNil c)))
  (let-match erased q (PTCons _ _ z _ l2r qy q1))
  (PTCons c x z lr l2r (pcomp-c a b c x y z pc px qy) (permt-comp a b c lr l1r l2r pc p1 q1)))

; Two colour permutations taking e to C1 differ by p123 or p132.
(def-fns _ $ (erased fix-c1 : (erased (Perm) a b) (erased (Col) e) (erased (IsPerm a) ia) (erased (IsPerm b) ib) (erased (PermC a e (C1)) pa)
    (erased (PermC b e (C1)) pb) -> (erased (Or (PComp a p123 b) (PComp a p132 b)) r))
  (match erased ia _
    ((IP123) (let-match erased pa (PC1 _ _ _)) (let-match erased pb (PC1 _ _ _))
      (match erased ib _
        ((IP123) (InL _ _ (MkPComp _ _ _ _ _ _ _ (PC1 _ _ _) (PC2 _ _ _) (PC3 _ _ _))))
        ((IP132) (InR _ _ (MkPComp _ _ _ _ _ _ _ (PC1 _ _ _) (PC2 _ _ _) (PC3 _ _ _))))))
    ((IP132) (let-match erased pa (PC1 _ _ _)) (let-match erased pb (PC1 _ _ _))
      (match erased ib _
        ((IP132) (InL _ _ (MkPComp _ _ _ _ _ _ _ (PC1 _ _ _) (PC3 _ _ _) (PC2 _ _ _))))
        ((IP123) (InR _ _ (MkPComp _ _ _ _ _ _ _ (PC1 _ _ _) (PC3 _ _ _) (PC2 _ _ _))))))
    ((IP213) (let-match erased pa (PC2 _ _ _)) (let-match erased pb (PC2 _ _ _))
      (match erased ib _
        ((IP213) (InL _ _ (MkPComp _ _ _ _ _ _ _ (PC2 _ _ _) (PC1 _ _ _) (PC3 _ _ _))))
        ((IP312) (InR _ _ (MkPComp _ _ _ _ _ _ _ (PC2 _ _ _) (PC1 _ _ _) (PC3 _ _ _))))))
    ((IP231) (let-match erased pa (PC3 _ _ _)) (let-match erased pb (PC3 _ _ _))
      (match erased ib _
        ((IP231) (InL _ _ (MkPComp _ _ _ _ _ _ _ (PC2 _ _ _) (PC3 _ _ _) (PC1 _ _ _))))
        ((IP321) (InR _ _ (MkPComp _ _ _ _ _ _ _ (PC2 _ _ _) (PC3 _ _ _) (PC1 _ _ _))))))
    ((IP312) (let-match erased pa (PC2 _ _ _)) (let-match erased pb (PC2 _ _ _))
      (match erased ib _
        ((IP312) (InL _ _ (MkPComp _ _ _ _ _ _ _ (PC3 _ _ _) (PC1 _ _ _) (PC2 _ _ _))))
        ((IP213) (InR _ _ (MkPComp _ _ _ _ _ _ _ (PC3 _ _ _) (PC1 _ _ _) (PC2 _ _ _))))))
    ((IP321) (let-match erased pa (PC3 _ _ _)) (let-match erased pb (PC3 _ _ _))
      (match erased ib _
        ((IP321) (InL _ _ (MkPComp _ _ _ _ _ _ _ (PC3 _ _ _) (PC2 _ _ _) (PC1 _ _ _))))
        ((IP231) (InR _ _ (MkPComp _ _ _ _ _ _ _ (PC3 _ _ _) (PC2 _ _ _) (PC1 _ _ _))))))))

; The traces of the permuted tree tp are those whose image under g is a trace of t (the other direction of perm-mem).
(def-fns _ $ (erased perm-mem-back : (erased (Perm) g) (erased (Ctree) t tp) (subterm erased (List (Col)) w) (erased (List (Col)) l) (subterm erased (CtPerm g t tp) p)
    (erased (PermT g w l) pt) (erased (CtMem t l) m) -> (erased (CtMem tp w) r))
  (match erased p _
    (absurd (CPE _) (mem-empty l m))
    ((CPL _ lf) (let-match erased (leaf-mem-nil lf l m) (Refl _ _)) (let-match erased pt (PTNil _)) m)
    ((CPN g1 g2 g3 t1 t2 t3 u1 u2 u3 a1 a2 a3 _ s1 s2 s3 p1 p2 p3 c)
      (let-match erased pt (PTCons _ e d w1 l1 pc pt1)
        (absurd (PTNil _) (let-match erased m (MkCtMem _ _ n s)) (let-match erased s (SubNil _ _ rt)) rt))
      (let ((erased tt)) (CNode t1 t2 t3))
      (match erased pc _
        (absurd (PC0 _) (mem-empty l1 (mem-sel tt (CEmpty) d l1 m (SelN0 t1 t2 t3))))
        ((PC1 _ _ _) (mem-cons tp a1 e w1 (cons-sel-back a1 a2 a3 tp a1 e c (SelN1 a1 a2 a3)) (perm-mem-back g u1 a1 w1 l1 p1 pt1 (mem-sel tt u1 d l1 m s1))))
        ((PC2 _ _ _) (mem-cons tp a2 e w1 (cons-sel-back a1 a2 a3 tp a2 e c (SelN2 a1 a2 a3)) (perm-mem-back g u2 a2 w1 l1 p2 pt1 (mem-sel tt u2 d l1 m s2))))
        ((PC3 _ _ _) (mem-cons tp a3 e w1 (cons-sel-back a1 a2 a3 tp a3 e c (SelN3 a1 a2 a3)) (perm-mem-back g u3 a3 w1 l1 p3 pt1 (mem-sel tt u3 d l1 m s3))))))))

(def-fns _ $ (erased evtail-fn : (erased (List (Col)) l) (erased (Bool) b b2) (subterm erased (EvenTail l b) p) (erased (EvenTail l b2) q) -> (erased (Eq (Bool) b b2) e))
  (match erased p _
    ((ETNil) (let-match erased q (ETNil)) (Refl _ b))
    ((ET0 l1 _ p1) (let-match erased q (ET0 _ _ q1)) (evtail-fn l1 b b2 p1 q1))
    ((ET1 l1 _ p1) (let-match erased q (ET1 _ _ q1)) (evtail-fn l1 b b2 p1 q1))
    ((ET2 _) (let-match erased q (ET2 _)) (Refl _ b))
    ((ET3 _) (let-match erased q (ET3 _)) (Refl _ b))))

; An even tail that stays even under p132 has neither C2 nor C3.
(def-fns _ $ (erased ev-p132 : (erased (List (Col)) x y) (subterm erased (EvenTail x (BTrue)) ex) (erased (PermT p132 x y) pt) (erased (EvenTail y (BTrue)) ey)
    -> (erased (Eq (List (Col)) y x) e))
  (let-match erased pt (PTCons _ c d x1 y1 pc pt1) ((PTNil _) (Refl _ y)))
  (match erased ex _
    ((ET0 _ _ ex1) (let-match erased pc (PC0 _)) (let-match erased ey (ET0 _ _ ey1)) (let-match erased (ev-p132 x1 y1 ex1 pt1 ey1) (Refl _ _)) (Refl _ y))
    ((ET1 _ _ ex1) (let-match erased pc (PC1 _ _ _)) (let-match erased ey (ET1 _ _ ey1)) (let-match erased (ev-p132 x1 y1 ex1 pt1 ey1) (Refl _ _)) (Refl _ y))
    (absurd (ET2 _) (let-match erased pc (PC2 _ _ _)) ey)))

; The tree t0 of cpcolor0-c holds rest, normalised by any colour permutation taking e1 to C1 to an even tail, for a trace
; e0 :: e1 :: rest that the steps rcp can give from c c.
(def-fns _ $ (erased core-mem : (erased (List (Step)) rcp) (erased (Ctree) t0) (erased (Cov0 rcp t0) cv) (erased (Col) c e0 e1) (erased (List (Col)) rest l2)
    (erased (StepsTr rcp (Cons (Col) c (Cons (Col) c (Nil (Col)))) (Cons (Col) e0 (Cons (Col) e1 rest))) st) (erased (NZ c) nz)
    (erased (AllNZ (Cons (Col) e0 (Cons (Col) e1 rest))) a) (erased (Perm) rho) (erased (IsPerm rho) irho) (erased (PermC rho e1 (C1)) prho)
    (erased (PermT rho rest l2) ptr) (erased (EvenTail l2 (BTrue)) evl) -> (erased (CtMem t0 l2) r))
  (let ((erased p) (erased ip) (erased pet) (erased pt) (erased bm)) (cov0-mem rcp c _ t0 cv st nz))
  (let-match erased pt (PTCons _ _ x _ pr pc0 pt1))
  (let-match erased pt1 (PTCons _ _ y _ prest pc1 pt2))
  (let-match erased bm (MkBrMem _ _ _ grest _ g ig pg pgt nm))
  (let-match erased a (AllNZCons _ _ _ a1))
  (let-match erased a1 (AllNZCons _ _ nz1 a2))
  (let ((erased A) (erased pcA) (erased iA)) (pcomp-ex p g ip ig))
  (let ((erased ptA)) (permt-comp p g A rest prest grest pcA pt2 pgt))
  (let-match erased nm (NMIn _ _ q nq mq) (absurd (NMZ _ _ z) (allnz-hasc0 grest (allnz-perm A rest grest iA ptA a2) z)))
  (match erased (fix-c1 A rho e1 iA irho (pcomp-c p g A e1 y (C1) pcA pc1 pg) prho) _
    ((InL _ _ k)
      (let-match erased (permt-fn rho rest l2 grest ptr (permt-comp A p123 rho rest grest grest k ptA (tail-id grest))) (Refl _ _))
      (match erased nq _
        ((NrEven _ _) mq)
        (absurd (NrOdd _ _ e _) (match erased (evtail-fn grest (BTrue) (BFalse) evl e) _))))
    ((InR _ _ k)
      (let ((erased z) (erased ptz)) (permt-ex p132 grest (IP132)))
      (let-match erased (permt-fn rho rest l2 z ptr (permt-comp A p132 rho rest grest z k ptA ptz)) (Refl _ _))
      (match erased nq _
        ((NrEven _ e) (let-match erased (ev-p132 grest l2 e ptz evl) (Refl _ _)) mq)
        ((NrOdd _ _ _ qq) (let-match erased (permt-fn p132 grest q l2 qq ptz) (Refl _ _)) mq)))))

; The tree of cpcolor-c holds every even trace e1 :: rest for which e0 :: e1 :: rest is reached from c c by its steps.
(def-fns _ $ (erased comp-mem : (erased (List (Step)) rcp) (erased (Ctree) t0 ta tb t) (erased (Cov0 rcp t0) cv) (erased (CtCons t0 ta tb t) cc)
    (erased (CtPerm p312 t0 ta) pa) (erased (CtPerm p231 t0 tb) pb) (erased (Col) c e0 e1) (erased (List (Col)) rest)
    (erased (StepsTr rcp (Cons (Col) c (Cons (Col) c (Nil (Col)))) (Cons (Col) e0 (Cons (Col) e1 rest))) st) (erased (NZ c) nz)
    (erased (AllNZ (Cons (Col) e0 (Cons (Col) e1 rest))) a) (erased (EvenT (Cons (Col) e1 rest) (BTrue)) ev) -> (erased (CtMem t (Cons (Col) e1 rest)) r))
  (let-match erased a (AllNZCons _ _ _ a1))
  (let-match erased a1 (AllNZCons _ _ nz1 _))
  (match erased ev _
    (absurd (Ev0 _) nz1)
    ((Ev1 _ _ el) (mem-cons t t0 e1 rest (cons-sel-back t0 ta tb t t0 e1 cc (SelN1 t0 ta tb))
      (core-mem rcp t0 cv c e0 e1 rest rest st nz a p123 (IP123) (PC1 (C1) (C2) (C3)) (tail-id rest) el)))
    ((Ev2 _ l2 _ q el) (mem-cons t ta e1 rest (cons-sel-back t0 ta tb t ta e1 cc (SelN2 t0 ta tb))
      (perm-mem-back p312 t0 ta rest l2 pa q (core-mem rcp t0 cv c e0 e1 rest l2 st nz a p312 (IP312) (PC2 (C3) (C1) (C2)) q el))))
    ((Ev3 _ l2 _ q el) (mem-cons t tb e1 rest (cons-sel-back t0 ta tb t tb e1 cc (SelN3 t0 ta tb))
      (perm-mem-back p231 t0 tb rest l2 pb q (core-mem rcp t0 cv c e0 e1 rest l2 st nz a p231 (IP231) (PC3 (C2) (C3) (C1)) q el))))))

(def-fns _ $ (erased steps-snoc : (erased (Step) s) (erased (List (Step)) cp1 cp2) (erased (List (Col)) a b c) (subterm erased (Snoc (Step) cp1 s cp2) sn)
    (erased (StepsTr cp1 a b) st) (erased (StepTr s b c) s1) -> (erased (StepsTr cp2 a c) r))
  (match erased sn _
    ((SnocNil _ _) (let-match erased st (SNil _)) (SCons s (Nil (Step)) a c c s1 (SNil c)))
    ((SnocCons _ s0 _ xs ys sn1)
      (let-match erased st (SCons _ _ _ a1 _ st0 rest))
      (SCons s0 ys a a1 c st0 (steps-snoc s xs ys a1 b c sn1 rest s1)))))

(def-fns _ $ (erased differ-cce : (erased (List (Nat)) ke ks) (erased (Nat) x) (subterm erased (Differ ke ks) df) -> (erased (CcEdge (Nil (Nat)) x ke ks) r))
  (let-match erased df (DifferCons ke1 ks1 a b ne df1) ((DifferNil) (CENil (Nil (Nat)) x)))
  (CEOut (Nil (Nat)) ke1 ks1 x a b (NotInNil x) ne (differ-cce ke1 ks1 (Succ x) df1)))

(def-fns _ $ (erased flag-nz : (erased (Nat) x) (erased (Col) u) (erased (Flag (Nil (Nat)) x u) fl) -> (erased (NZ u) r))
  (match erased fl _ (absurd (FlIn _ _ p) p) ((FlOut _ _ _ _ nz) nz)))

; The ring trace et that a colouring ks of a map, seen from the map of the cubic program cp, gives that map, with the run
; of the steps of cp, read backwards as rcp, that makes it from the trace c c of the first map.
(def-fns _ $ (erased steps-hit : (erased (List (Step)) cp) (erased (Nat) d) (erased (List (Nat)) e f r ks big) (subterm erased (Cpmap cp d e f r) cm)
    (erased (CubicProg cp) cq) (erased (Ctx (Nil (Nat)) ks big e f) ctx)
    -> (erased (List (Nat)) rc) (erased (List (Col)) cs et) (erased (Respects ks r rc) rr) (erased (NCols rc cs) nc) (erased (Trace cs et) tr)
    (erased (List (Step)) rcp) (erased (RevApp (Step) cp (Nil (Step)) rcp) ra) (erased (Col) c) (erased (NZ c) nzc)
    (erased (StepsTr rcp (Cons (Col) c (Cons (Col) c (Nil (Col)))) et) st))
  (let ((erased ie)) (Nil (Nat)))
  (match erased cm _
    ((CmNil)
      (let ((erased o) (erased z)) (values (Succ (Zero)) (Zero)))
      (let ((erased pe)) (NthThere _ o (Cons (Nat) z (Nil (Nat))) z z (NthHere _ z (Nil (Nat)))))
      (let ((erased k1) (erased pk1) (erased c1) (erased q1)) (ctx-col ie ks big e f o z ctx pe))
      (let ((erased k0) (erased pk0) (erased c0) (erased q0)) (ctx-col ie ks big e f z o ctx (NthHere _ o (Cons (Nat) z (Nil (Nat))))))
      (let ((erased u) (erased pu)) (addc-c c1 c0))
      (let ((erased fl)) (flag-of ie ks big e f o z z k1 k0 c1 c0 u ctx pe (NthHere _ z (Cons (Nat) o (Nil (Nat)))) pk1 pk0 q1 q0 pu))
      (values (Cons (Nat) k1 (Cons (Nat) k0 (Nil (Nat)))) (Cons (Col) c1 (Cons (Col) c0 (Nil (Col)))) (Cons (Col) u (Cons (Col) u (Nil (Col))))
        (RespCons ks (Cons (Nat) z (Nil (Nat))) (Cons (Nat) k0 (Nil (Nat))) o k1 pk1 (RespCons ks (Nil (Nat)) (Nil (Nat)) z k0 pk0 (RespNil ks)))
        (NCsCons k1 c1 _ _ q1 (NCsCons k0 c0 _ _ q0 (NCsNil)))
        (MkTrace c1 _ _ (CTStep c1 c1 c0 u _ _ pu (CTLast c1 c0 u (addc-comm c1 c0 u pu))))
        (Nil (Step)) (RANil (Step) (Nil (Step))) u (flag-nz o u fl) (SNil _)))
    ((CmR k _ cp1 _ _ r1 _ c1 rt)
      (let-match erased cq (CubR _ _ cq1))
      (let ((erased rc1) (erased cs1) (erased et1) (erased rr1) (erased nc1) (erased tr1) (erased rcp1) (erased ra1) (erased c) (erased nzc) (erased st1))
        (steps-hit cp1 d e f r1 ks big c1 cq1 ctx))
      (let ((erased rc) (erased cs) (erased et) (erased rr) (erased nc) (erased tr) (erased rte)) (ring-rot k ks r1 r rc1 cs1 et1 rt rr1 nc1 tr1))
      (let ((erased s) (erased cp2)) (values (SR k) (Cons (Step) (SR k) cp1)))
      (let ((erased rcp) (erased ra)) (revapp-exists (Step) cp1 (Cons (Step) s (Nil (Step)))))
      (values rc cs et rr nc tr rcp (RACons (Step) s cp1 (Nil (Step)) rcp ra) c nzc
        (steps-snoc s rcp1 rcp _ et1 et (revapp-snoc (Step) s cp1 (Nil (Step)) _ rcp1 rcp ra1 (SnocNil _ s) ra) st1 (STR k et1 et rte))))
    (absurd (CmRr _ _ _ _ _ _ _ _ _ _) cq)
    (absurd (CmK _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) cq)
    ((CmU d0 cp1 e0 f0 r0 _ _ _ c1 u)
      (let-match erased cq (CubU _ cq1))
      (let ((erased n0) (erased pm0)) (cpmap-map cp1 d0 e0 f0 r0 c1))
      (let ((erased ctx0)) (ctx-unu d0 e0 n0 f0 r0 e f r ie ks big pm0 u ctx))
      (let ((erased rc0) (erased cs0) (erased et0) (erased rr0) (erased nc0) (erased tr0) (erased rcp1) (erased ra1) (erased c) (erased nzc) (erased st1))
        (steps-hit cp1 d0 e0 f0 r0 ks big c1 cq1 ctx0))
      (let ((erased uu) (erased rc1) (erased cs1) (erased rr1) (erased nc1) (erased tr1) (erased fl1))
        (u-trace d0 e0 n0 f0 r0 e f r ie ks big rc0 cs0 et0 pm0 u ctx rr0 nc0 tr0))
      (let ((erased s)) (SU))
      (let ((erased rcp) (erased ra)) (revapp-exists (Step) cp1 (Cons (Step) s (Nil (Step)))))
      (values rc1 cs1 (Cons (Col) uu (Cons (Col) uu et0)) rr1 nc1 tr1 rcp (RACons (Step) s cp1 (Nil (Step)) rcp ra) c nzc
        (steps-snoc s rcp1 rcp _ et0 _ (revapp-snoc (Step) s cp1 (Nil (Step)) _ rcp1 rcp ra1 (SnocNil _ s) ra) st1 (STU uu et0 (flag-nz (Succ d0) uu fl1)))))
    ((CmY d0 cp1 e0 f0 r0 e1 f1 r1 _ _ _ c1 u nn)
      (let-match erased cq (CubY _ cq1))
      (let ((erased n0) (erased pm0)) (cpmap-map cp1 d0 e0 f0 r0 c1))
      (let ((erased n1) (erased pm1)) (ecpU-map d0 e0 n0 f0 r0 e1 f1 r1 pm0 u))
      (let ((erased ctx1)) (ctx-unn (Succ (Succ d0)) e1 n1 f1 r1 e f r ie ks big pm1 nn ctx))
      (let ((erased ctx0)) (ctx-unu d0 e0 n0 f0 r0 e1 f1 r1 ie ks big pm0 u ctx1))
      (let ((erased rc0) (erased cs0) (erased et0) (erased rr0) (erased nc0) (erased tr0) (erased rcp1) (erased ra1) (erased c) (erased nzc) (erased st1))
        (steps-hit cp1 d0 e0 f0 r0 ks big c1 cq1 ctx0))
      (let ((erased k) (erased lk) (erased csz)) (cpmap-size cp1 d0 e0 f0 r0 c1))
      (let-match erased (cprsize-proper cp1 k csz cq1) (LtS _ k1 _))
      (let-match erased (trace-length cs0 et0 k tr0 (ncols-length rc0 cs0 k nc0 (respects-length ks r0 rc0 k rr0 lk))) (LengthCons _ a1 et2 _ _))
      (let ((erased uu) (erased rc1) (erased cs1) (erased rr1) (erased nc1) (erased tr1) (erased fl1))
        (u-trace d0 e0 n0 f0 r0 e1 f1 r1 ie ks big rc0 cs0 et0 pm0 u ctx1 rr0 nc0 tr0))
      (let ((erased s) (erased ps) (erased rc2) (erased cs2) (erased rr2) (erased nc2) (erased tr2) (erased fl2))
        (n-trace (Succ (Succ d0)) e1 n1 f1 r1 e f r ie ks big rc1 cs1 et2 uu uu a1 pm1 nn ctx rr1 nc1 tr1))
      (let ((erased sy)) (SY))
      (let ((erased rcp) (erased ra)) (revapp-exists (Step) cp1 (Cons (Step) sy (Nil (Step)))))
      (values rc2 cs2 (Cons (Col) uu (Cons (Col) s et2)) rr2 nc2 tr2 rcp (RACons (Step) sy cp1 (Nil (Step)) rcp ra) c nzc
        (steps-snoc sy rcp1 rcp _ et0 _ (revapp-snoc (Step) sy cp1 (Nil (Step)) _ rcp1 rcp ra1 (SnocNil _ sy) ra) st1
          (STY a1 uu s et2 (addc-comm uu a1 s ps) (flag-nz (Succ d0) uu fl1) (flag-nz (Succ (Succ d0)) s fl2)))))
    ((CmH d0 cp1 e0 f0 r0 e1 f1 r1 e5 f5 r5 _ _ _ c1 u nn nn2)
      (let-match erased cq (CubH _ cq1))
      (let ((erased d2) (erased d4)) (values (Succ (Succ d0)) (Succ (Succ (Succ (Succ d0))))))
      (let ((erased n0) (erased pm0)) (cpmap-map cp1 d0 e0 f0 r0 c1))
      (let ((erased n1) (erased pm1)) (ecpU-map d0 e0 n0 f0 r0 e1 f1 r1 pm0 u))
      (let ((erased n5) (erased pm5)) (ecpN-map d2 e1 n1 f1 r1 e5 f5 r5 pm1 nn))
      (let ((erased ctx5)) (ctx-unn d4 e5 n5 f5 r5 e f r ie ks big pm5 nn2 ctx))
      (let ((erased ctx1)) (ctx-unn d2 e1 n1 f1 r1 e5 f5 r5 ie ks big pm1 nn ctx5))
      (let ((erased ctx0)) (ctx-unu d0 e0 n0 f0 r0 e1 f1 r1 ie ks big pm0 u ctx1))
      (let ((erased rc0) (erased cs0) (erased et0) (erased rr0) (erased nc0) (erased tr0) (erased rcp1) (erased ra1) (erased c) (erased nzc) (erased st1))
        (steps-hit cp1 d0 e0 f0 r0 ks big c1 cq1 ctx0))
      (let ((erased k) (erased lk) (erased csz)) (cpmap-size cp1 d0 e0 f0 r0 c1))
      (let-match erased (cprsize-proper cp1 k csz cq1) (LtS _ k1 lk1))
      (let-match erased lk1 (LtZ k2))
      (let-match erased (trace-length cs0 et0 k tr0 (ncols-length rc0 cs0 k nc0 (respects-length ks r0 rc0 k rr0 lk))) (LengthCons _ a1 et1 _ l1))
      (let-match erased l1 (LengthCons _ a2 et2 _ _))
      (let ((erased uu) (erased rc1) (erased cs1) (erased rr1) (erased nc1) (erased tr1) (erased fl1))
        (u-trace d0 e0 n0 f0 r0 e1 f1 r1 ie ks big rc0 cs0 et0 pm0 u ctx1 rr0 nc0 tr0))
      (let ((erased v) (erased pv) (erased rc5) (erased cs5) (erased rr5) (erased nc5) (erased tr5) (erased fl2))
        (n-trace d2 e1 n1 f1 r1 e5 f5 r5 ie ks big rc1 cs1 et1 uu uu a1 pm1 nn ctx5 rr1 nc1 tr1))
      (let ((erased w) (erased pw) (erased rc2) (erased cs2) (erased rr2) (erased nc2) (erased tr2) (erased fl3))
        (n-trace d4 e5 n5 f5 r5 e f r ie ks big rc5 cs5 et2 uu v a2 pm5 nn2 ctx rr5 nc5 tr5))
      (let ((erased ee) (erased pee)) (addc-c a1 a2))
      (let ((erased pv2)) (addc-comm uu a1 v pv))
      (let ((erased sh)) (SH))
      (let ((erased rcp) (erased ra)) (revapp-exists (Step) cp1 (Cons (Step) sh (Nil (Step)))))
      (values rc2 cs2 (Cons (Col) uu (Cons (Col) w et2)) rr2 nc2 tr2 rcp (RACons (Step) sh cp1 (Nil (Step)) rcp ra) c nzc
        (steps-snoc sh rcp1 rcp _ et0 _ (revapp-snoc (Step) sh cp1 (Nil (Step)) _ rcp1 rcp ra1 (SnocNil _ sh) ra) st1
          (STH a1 a2 ee uu v w et2 pee pv2 (addc-swap a1 uu a2 v w ee pv2 pw pee) (flag-nz (Succ d0) uu fl1) (flag-nz d2 v fl2) (flag-nz d4 w fl3)))))))

; The completeness half of ctree_mem_cpcolor of cfcolor.v: the tree cpcolor-c computes for a cubic program holds every
; even trace et with e0 :: et a ring trace of a colouring of the program's map.
(def-fns _ $ (erased cpcolor-mem : (erased (List (Step)) cp) (erased (Ctree) t) (erased (CpComp cp t) comp) (erased (CubicProg cp) cq) (erased (Col) e0)
    (erased (List (Col)) et) (erased (CpCol cp (Cons (Col) e0 et)) cc) (erased (EvenT et (BTrue)) ev) -> (erased (CtMem t et) r))
  (let ((erased a)) (cpcol-nz cp _ cc))
  (let ((erased k) (erased lk) (erased csk)) (cpcol-length cp _ cc))
  (let-match erased cc (MkCpCol _ d e f r ks rc cs _ cm col rr nc tr))
  (let-match erased comp (MkCpComp _ rcp t0 ta tb _ rac cv c pa pb))
  (let ((erased n) (erased pm)) (cpmap-map cp d e f r cm))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f (pointed-hyper d e n f r pm)))
  (let-match erased col (MkFourColoring _ _ _ ke face ce edge four))
  (let ((erased ctx)) (MkCtx (Nil (Nat)) ks e e f ke d (pre-refl e) (MkFC ks f ks face (pre-refl ks)) ce (differ-cce ke ks (Zero) edge) four
    (respects-length ks f ks d face lf) le))
  (let ((erased rc2) (erased cs2) (erased et2) (erased rr2) (erased nc2) (erased tr2) (erased rcp2) (erased ra2) (erased c0) (erased nzc) (erased st))
    (steps-hit cp d e f r ks e cm cq ctx))
  (let-match erased (respects-fn ks r rc rc2 rr rr2) (Refl _ _))
  (let-match erased (ncols-fn rc cs cs2 nc nc2) (Refl _ _))
  (let-match erased (trace-fn cs _ et2 tr tr2) (Refl _ _))
  (let-match erased (revapp-fn (Step) cp (Nil (Step)) rcp2 rcp ra2 (revapp-flip (Step) rcp (Nil (Step)) cp rcp rac (RANil (Step) rcp))) (Refl _ _))
  (let-match erased (cprsize-proper cp k csk cq) (LtS _ k1 lt1))
  (let-match erased lt1 (LtZ _))
  (let-match erased lk (LengthCons _ _ _ _ lk1))
  (let-match erased lk1 (LengthCons _ e1 rest _ _))
  (comp-mem rcp t0 ta tb t cv c pa pb c0 e0 e1 rest st nzc a ev))

(def-fns _ $ (erased even-ex : (erased (List (Col)) et) -> (erased (Bool) b) (erased (EvenT et b) ev))
  (match erased et _
    ((Nil _) (values (BTrue) (EvNil)))
    ((Cons _ c l)
      (match erased c _
        ((C0) (values (BTrue) (Ev0 l)))
        ((C1) (let ((erased b) (erased p)) (eventail-c l)) (values b (Ev1 l b p)))
        ((C2) (let ((erased l2) (erased q)) (permt-c p312 l)) (let ((erased b) (erased p)) (eventail-c l2)) (values b (Ev2 l l2 b q p)))
        ((C3) (let ((erased l2) (erased q)) (permt-c p231 l)) (let ((erased b) (erased p)) (eventail-c l2)) (values b (Ev3 l l2 b q p)))))))

; The even normal form of the trace, without its first entry, of every colouring of the map of a cubic program is in the tree
; cpcolor-c computes for it.
(def-fns _ $ (erased cpcolor-etrace : (erased (List (Step)) cp) (erased (Ctree) t) (erased (CpComp cp t) comp) (erased (CubicProg cp) cq) (erased (Col) e0)
    (erased (List (Col)) et et2) (erased (CpCol cp (Cons (Col) e0 et)) cc) (erased (ETrace et et2) etr) -> (erased (CtMem t et2) r))
  (let ((erased b) (erased ev)) (even-ex et2))
  (let-match erased (erun-fn (ESStart) et2 b (BTrue) (even-run et2 b ev) (etrace-run et et2 etr)) (Refl _ _))
  (match erased etr _
    ((ETrEven _ _) (cpcolor-mem cp t comp cq e0 et cc ev))
    ((ETrOdd _ _ _ q)
      (let ((erased e2) (erased pe)) (permc-ex p132 e0 (IP132)))
      (cpcolor-mem cp t comp cq e2 et2 (cpcol-perm cp _ _ p132 cc (IP132) (PTCons p132 e0 e2 et et2 pe q)) ev))))
