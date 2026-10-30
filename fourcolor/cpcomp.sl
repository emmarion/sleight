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
