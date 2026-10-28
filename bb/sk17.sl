(let ((many p17)) (Cons _ (Def (Mov (BTrue) (DR) 1)) $ Cons _ (Undef) $ Cons _ (Def (Mov (BFalse) (DL) 2)) $ Cons _ (Def (Mov (BTrue) (DR) 4)) $
  Cons _ (Def (Mov (BFalse) (DL) 3)) $ Cons _ (Def (Mov (BTrue) (DL) 2)) $ Cons _ (Def (Mov (BTrue) (DR) 0)) $ Cons _ (Def (Mov (BTrue) (DL) 1)) $
  Cons _ (Def (Mov (BFalse) (DR) 1)) $ Cons _ (Def (Mov (BFalse) (DR) 0)) $ Nil (PT)))

(sk-family Sk17 MkSk17 sk17-of ()
  (t-l1 (2 DL "1" TV "" TV) (2 DL "" TV "1" TV))
  (t-l2 (2 DL "0101" TV "" TV) (2 DL "" TV "1010" TV))
  (t-turn (2 DL "011" TV "" TV) (1 DR "101" TV "" TV))
  (t-r10 (1 DR "" TV "10" TV) (1 DR "01" TV "" TV))
  (t-r110 (1 DR "" TV "110" TV) (1 DR "101" TV "" TV))
  (t-end (1 DR "" TV "0" TZ) (2 DL "" TV "0" TZ))
  (t-end1 (1 DR "" TV "10" TZ) (2 DL "01" TV "0" TZ))
  (t-zero (2 DL "" TZ "" TV) (1 DR "11" TZ "" TV))
  (t-ovf (2 DL "01" TZ "" TV) (1 DR "0110111" TZ "" TV))
  (t-init ((Zero) DR "" TZ "" TZ) (2 DL "101010101101011" TZ "0" TZ)))
(comptime-match many (sk17-of p17) (ROk _ sg17))

(def-adts
  ((Rp : ((Bool) x) ((Bool) y) ((Nat) n) ((List (Bool)) t) ((List (Bool)) b) -> Type)
    enum
    (many RpZ : (erased (Bool) x y) (erased (List (Bool)) t) -> (Rp x y (Zero) t t))
    (many RpS : (erased (Bool) x y) (erased (Nat) n) (erased (List (Bool)) t b) (erased (Rp x y n t b) g)
       -> (Rp x y (Succ n) t (Cons (Bool) x (Cons (Bool) y b))))))

(def-fns _ $ (erased rp-shift : (erased (Bool) x y) (erased (Nat) n) (erased (List (Bool)) t b) (subterm erased (Rp x y n (Cons (Bool) x (Cons (Bool) y t)) b) g)
    -> (erased (Rp x y (Succ n) t b) h))
  (match erased g _
    ((RpZ _ _ _) (RpS x y (Zero) t t (RpZ x y t)))
    ((RpS _ _ n1 _ b1 g1) (RpS x y (Succ n1) t b1 (rp-shift x y n1 t b1 g1)))))

(def-fns _ $ (erased rp-unshift : (erased (Bool) x y) (erased (Nat) n) (erased (List (Bool)) t b) (subterm erased (Rp x y (Succ n) t b) g)
    -> (erased (Rp x y n (Cons (Bool) x (Cons (Bool) y t)) b) h))
  (let-match erased g (RpS _ _ _ _ b1 g1))
  (match erased g1 _
    ((RpZ _ _ _) (RpZ x y b))
    ((RpS _ _ n1 _ b2 g2) (RpS x y n1 (Cons (Bool) x (Cons (Bool) y t)) b1 (rp-unshift x y n1 t b1 g1)))))

(def-fns _ $ (erased rp-ex : (erased (Bool) x y) (subterm erased (Nat) n) (erased (List (Bool)) t) -> (erased (List (Bool)) b) (erased (Rp x y n t b) g))
  (let-match erased n (Succ n1) ((Zero) (values t (RpZ x y t))))
  (let ((erased b1) (erased g1)) (rp-ex x y n1 t))
  (values (Cons (Bool) x (Cons (Bool) y b1)) (RpS x y n1 t b1 g1)))

(def-fns _ $ (erased rcat : (erased (Tc) e1 e2 e3) (erased (Bool) g1 g2) (erased (Reach p17 e1 e2 g1) ra) (erased (Reach p17 e2 e3 g2) rb)
    -> (erased (Bool) g) (erased (Reach p17 e1 e3 g) r))
  (let ((erased g) (erased _) (erased r)) (reach-cat p17 e1 e2 e3 g1 g2 ra rb))
  (values g r))

(def-fns _ $ (erased go-r10 : (erased (Nat) n) (erased (List (Bool)) l r R) (subterm erased (Rp (BTrue) (BFalse) n r R) g)
    -> (erased (List (Bool)) L) (erased (Rp (BFalse) (BTrue) n l L) h) (erased (Bool) gf) (erased (Reach p17 (MkTc 1 (DR) l R) (MkTc 1 (DR) L r) gf) rc))
  (let-match erased g (RpS _ _ n1 _ R1 g1) ((RpZ _ _ _) (values l (RpZ _ _ l) (BFalse) (reach-refl p17 _))))
  (let ((erased L) (erased h) (erased gf) (erased rc)) (go-r10 n1 (bits "01" l) r R1 g1))
  (values L (rp-shift _ _ n1 l L h) (BTrue) (reach-catT p17 _ _ _ _ (t-r10 p17 sg17 l R1) rc)))

(def-adts
  ((PB : ((Nat) n) ((Bool) b) -> Type)
    enum
    (many PB0 : -> (PB (Zero) (BFalse)))
    (many PBF : (erased (Nat) n) (erased (PB n (BTrue)) p) -> (PB (Succ n) (BFalse)))
    (many PBT : (erased (Nat) n) (erased (PB n (BFalse)) p) -> (PB (Succ n) (BTrue)))))

(def-fns _ $ (erased go-l-even : (erased (Nat) n) (erased (List (Bool)) l r L) (subterm erased (PB n (BFalse)) pe) (erased (Rp (BFalse) (BTrue) n l L) g)
    -> (erased (List (Bool)) R) (erased (Rp (BTrue) (BFalse) n r R) h) (erased (Bool) gf) (erased (Reach p17 (MkTc 2 (DL) L r) (MkTc 2 (DL) l R) gf) rc))
  (let-match erased pe (PBF n1 p1) ((PB0) (let-match erased g (RpZ _ _ _)) (values r (RpZ _ _ r) (BFalse) (reach-refl p17 _))))
  (let-match erased p1 (PBT n2 p2))
  (let-match erased g (RpS _ _ _ _ L1 g1))
  (let-match erased g1 (RpS _ _ _ _ L2 g2))
  (let ((erased R) (erased h) (erased gf) (erased rc)) (go-l-even n2 l (bits "1010" r) L2 p2 g2))
  (values R (rp-shift _ _ (Succ n2) r R (rp-shift _ _ n2 (bits "10" r) R h)) (BTrue) (reach-catT p17 _ _ _ _ (t-l2 p17 sg17 L2 r) rc)))

(def-fns _ $ (erased go-l-odd : (erased (Nat) n) (erased (List (Bool)) l r L) (erased (PB n (BFalse)) pe) (erased (Rp (BFalse) (BTrue) (Succ n) (Cons (Bool) (BTrue) l) L) g)
    -> (erased (List (Bool)) L2) (erased (Rp (BFalse) (BTrue) n (bits "101" l) L2) h) (erased (Reach p17 (MkTc 2 (DL) L r) (MkTc 1 (DR) L2 r) (BTrue)) rc))
  (let ((erased R) (erased h1) (erased g1) (erased rc1)) (go-l-even n (bits "011" l) r L pe (rp-unshift _ _ n _ L g)))
  (let ((erased L2) (erased h) (erased g2) (erased rc2)) (go-r10 n (bits "101" l) r R h1))
  (values L2 h (reach-cat2 p17 _ _ _ _ rc1 (reach-catT p17 _ _ _ _ (t-turn p17 sg17 l R) rc2))))

(def-fns _ $ (erased go-step : (erased (Nat) x Y) (erased (List (Bool)) T B R Rx) (erased (Rp (BFalse) (BTrue) Y T B) gb) (erased (Rp (BTrue) (BFalse) (Succ x) R Rx) gr)
    -> (erased (List (Bool)) B1 B2) (erased (Rp (BFalse) (BTrue) (Succ Y) T B1) h1) (erased (Rp (BFalse) (BTrue) x (Cons (Bool) (BTrue) B1) B2) h2)
    (erased (Reach p17 (MkTc 1 (DR) B (Cons (Bool) (BTrue) Rx)) (MkTc 1 (DR) B2 R) (BTrue)) rc))
  (let-match erased gr (RpS _ _ _ _ Rx1 gr1))
  (let ((erased B2) (erased h2) (erased g2) (erased rc2)) (go-r10 x (bits "101" B) R Rx1 gr1))
  (values (bits "01" B) B2 (RpS _ _ Y T B gb) h2 (reach-catT p17 _ _ _ _ (t-r110 p17 sg17 B Rx1) rc2)))

(def-adts
  ((Ls : ((List (Nat)) xs) ((List (Bool)) b) -> Type)
    enum
    (many LsN : -> (Ls (Nil (Nat)) (Nil (Bool))))
    (many LsC : (erased (Nat) y) (erased (List (Nat)) ys) (erased (List (Bool)) t b) (erased (Rp (BFalse) (BTrue) y t b) g) (erased (Ls ys t) s)
       -> (Ls (Cons (Nat) y ys) (Cons (Bool) (BTrue) b)))))

(def-adts
  ((Lw : ((List (Nat)) xs) ((List (Bool)) b) -> Type)
    enum
    (many MkLw : (erased (Nat) x) (erased (List (Nat)) xs) (erased (List (Bool)) t b) (erased (Rp (BFalse) (BTrue) x t b) g) (erased (Ls xs t) s)
       -> (Lw (Cons (Nat) x xs) b))))

(def-adts
  ((Sw : ((List (Nat)) xs) ((List (Nat)) ys) -> Type)
    enum
    (many SwOdd : (erased (Nat) y z) (erased (List (Nat)) zs) (erased (PB y (BTrue)) p) -> (Sw (Cons (Nat) y (Cons (Nat) z zs)) (Cons (Nat) y (Cons (Nat) (Succ z) zs))))
    (many SwEven : (erased (Nat) x) (erased (List (Nat)) xs ys) (erased (PB (Succ x) (BFalse)) p) (erased (Sw xs ys) w)
       -> (Sw (Cons (Nat) (Succ x) xs) (Cons (Nat) (Succ x) ys)))
    (many SwLast : (erased (Nat) y) (erased (PB y (BFalse)) p)
       -> (Sw (Cons (Nat) y (Nil (Nat))) (Cons (Nat) (Succ y) (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat)))))))
    (many SwOv : (erased (Nat) y) (erased (PB y (BTrue)) p)
       -> (Sw (Cons (Nat) y (Nil (Nat))) (Cons (Nat) (Succ y) (Cons (Nat) (Succ (Zero)) (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat))))))))))

(def-fns _ $ (erased ls-00 : -> (erased (Ls (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat)))) (bits "11")) s))
  (LsC (Zero) _ (bits "1") (bits "1") (RpZ _ _ _) (LsC (Zero) _ (Nil (Bool)) (Nil (Bool)) (RpZ _ _ _) (LsN))))

(def-fns _ $ (erased sweep : (erased (List (Nat)) cs cs2) (erased (List (Bool)) B R) (subterm erased (Sw cs cs2) w) (erased (Lw cs B) lw)
    -> (erased (Nat) h) (erased (List (Nat)) t) (erased (Eq (List (Nat)) cs2 (Cons (Nat) (Succ h) t)) e) (erased (List (Bool)) B2) (erased (Lw (Cons (Nat) h t) B2) lw2)
    (erased (Reach p17 (MkTc 2 (DL) B R) (MkTc 1 (DR) B2 R) (BTrue)) rc))
  (match erased w _
    ((SwOdd y z zs p)
      (let-match erased p (PBT y1 p1))
      (let-match erased lw (MkLw _ _ T _ g s))
      (let-match erased s (LsC _ _ T1 B1 g1 s1))
      (let ((erased B2) (erased h2) (erased rc)) (go-l-odd y1 B1 R B p1 g))
      (values y1 (Cons (Nat) (Succ z) zs) (Refl _ _) B2 (MkLw y1 _ _ B2 h2 (LsC (Succ z) zs T1 (bits "01" B1) (RpS _ _ z T1 B1 g1) s1)) rc))
    ((SwEven x xs ys p w1)
      (let-match erased lw (MkLw _ _ T _ g s))
      (let-match erased s (LsC y ys0 T0 B0 g0 s0) (absurd (LsN) w1))
      (let ((erased R1) (erased hr) (erased g1) (erased rc1)) (go-l-even (Succ x) (Cons (Bool) (BTrue) B0) R B p g))
      (let ((erased h1) (erased t1) (erased e1) (erased B1) (erased lw1) (erased rc2))
        (sweep xs ys B0 (Cons (Bool) (BTrue) R1) w1 (MkLw y ys0 T0 B0 g0 s0)))
      (let-match erased e1 (Refl _ _))
      (let-match erased lw1 (MkLw _ _ T2 _ g2 s2))
      (let ((erased B3) (erased B4) (erased k1) (erased k2) (erased rc3)) (go-step x h1 T2 B1 R R1 g2 hr))
      (values x (Cons (Nat) (Succ h1) t1) (Refl _ _) B4 (MkLw x _ _ B4 k2 (LsC (Succ h1) t1 T2 B3 k1 s2))
        (reach-cat2 p17 _ _ _ _ rc1 (reach-catT p17 _ _ _ _ (t-l1 p17 sg17 B0 R1) (reach-catT p17 _ _ _ _ rc2 rc3)))))
    ((SwLast y p)
      (let-match erased lw (MkLw _ _ T _ g s))
      (let-match erased s (LsN))
      (let ((erased R1) (erased hr) (erased g1) (erased rc1)) (go-l-even y (Nil (Bool)) R B p g))
      (let ((erased B2) (erased h2) (erased g2) (erased rc2)) (go-r10 y (bits "11") R R1 hr))
      (values y (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat)))) (Refl _ _) B2 (MkLw y _ _ B2 h2 (ls-00))
        (reach-cat2 p17 _ _ _ _ rc1 (reach-catT p17 _ _ _ _ (t-zero p17 sg17 (Nil (Bool)) R1) rc2))))
    ((SwOv y p)
      (let-match erased p (PBT y1 p1))
      (let-match erased lw (MkLw _ _ T _ g s))
      (let-match erased s (LsN))
      (let ((erased R1) (erased hr) (erased g1) (erased rc1)) (go-l-even y1 (bits "01") R B p1 (rp-unshift _ _ y1 _ B g)))
      (let ((erased B2) (erased h2) (erased g2) (erased rc2)) (go-r10 y1 (bits "0110111") R R1 hr))
      (values y (Cons (Nat) (Succ (Zero)) (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat))))) (Refl _ _) B2
        (MkLw y _ _ B2 (rp-shift _ _ y1 _ B2 h2) (LsC (Succ (Zero)) _ (bits "11") (bits "0111") (RpS _ _ (Zero) _ _ (RpZ _ _ _)) (ls-00)))
        (reach-cat2 p17 _ _ _ _ rc1 (reach-catT p17 _ _ _ _ (t-ovf p17 sg17 (Nil (Bool)) R1) rc2))))))

(def-adts
  ((EncA : ((Nat) f) ((List (Nat)) cs) ((List (Bool)) b) -> Type)
    enum
    (many EA0 : (erased (List (Nat)) cs) (erased (List (Bool)) b) (erased (Lw cs b) w) -> (EncA (Zero) cs b))
    (many EAS : (erased (Nat) y) (erased (List (Nat)) cs) (erased (List (Bool)) b) (erased (Lw (Cons (Nat) y cs) b) w) -> (EncA (Succ y) cs b))))

(def-fns _ $ (erased halve : (erased (Nat) c) (erased (List (Nat)) cs) (erased (List (Bool)) b) (erased (EncA (Zero) (Cons (Nat) c cs) b) ea) -> (erased (EncA (Succ c) cs b) ea2))
  (let-match erased ea (EA0 _ _ w))
  (EAS c cs b w))

(def-fns _ $ (erased tm-a : (erased (List (Nat)) cs cs2) (erased (Nat) h) (erased (List (Nat)) t) (erased (List (Bool)) B) (erased (Sw cs cs2) w)
    (erased (Eq (List (Nat)) cs2 (Cons (Nat) (Succ h) t)) e) (erased (Lw cs B) lw)
    -> (erased (List (Bool)) B2) (erased (Lw (Cons (Nat) h t) B2) lw2) (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) (BTrue)) rc))
  (let ((erased h1) (erased t1) (erased e1) (erased B2) (erased lw2) (erased rc)) (sweep cs cs2 B (bits "0") w lw))
  (let-match erased e (Refl _ _))
  (let-match erased e1 (Refl _ _))
  (values B2 lw2 (reach-catT p17 _ _ _ _ rc (t-end p17 sg17 B2 (Nil (Bool))))))

(def-fns _ $ (erased mstep-e : (erased (Nat) f c) (erased (List (Nat)) cs) (erased (List (Bool)) B) (erased (PB f (BTrue)) p) (erased (EncA (Succ f) (Cons (Nat) c cs) B) ea)
    -> (erased (List (Bool)) B2) (erased (EncA f (Cons (Nat) (Succ c) cs) B2) ea2) (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) (BTrue)) rc))
  (let-match erased ea (EAS _ _ _ lw))
  (let-match erased p (PBT f1 p1))
  (let ((erased B2) (erased lw2) (erased rc)) (tm-a _ _ f1 _ B (SwOdd f c cs p) (Refl _ _) lw))
  (values B2 (EAS f1 _ B2 lw2) rc))

(def-fns _ $ (erased mstep-o : (erased (Nat) f) (erased (List (Nat)) cs cs2) (erased (List (Bool)) B) (erased (PB f (BFalse)) p) (erased (Sw cs cs2) w) (erased (EncA (Succ f) cs B) ea)
    -> (erased (List (Bool)) B2) (erased (EncA f cs2 B2) ea2) (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) (BTrue)) rc))
  (let-match erased ea (EAS _ _ _ lw))
  (let-match erased p (PBF f1 p1)
    ((PB0)
      (let-match erased lw (MkLw _ _ T _ g s))
      (let-match erased g (RpZ _ _ _))
      (let-match erased s (LsC y ys T0 B0 g0 s0) (absurd (LsN) w))
      (let ((erased h) (erased t) (erased e) (erased B1) (erased lw1) (erased rc)) (sweep cs cs2 B0 (bits "10") w (MkLw y ys T0 B0 g0 s0)))
      (let-match erased e (Refl _ _))
      (let-match erased lw1 (MkLw _ _ T1 _ g1 s1))
      (values (bits "01" B1) (EA0 _ _ (MkLw (Succ h) t T1 _ (RpS _ _ h T1 B1 g1) s1))
        (reach-catT p17 _ _ _ _ (t-l1 p17 sg17 B0 (bits "0")) (reach-catT p17 _ _ _ _ rc (t-end1 p17 sg17 B1 (Nil (Bool))))))))
  (let ((erased B2) (erased lw2) (erased rc)) (tm-a _ _ f1 cs2 B (SwEven f1 cs cs2 p w) (Refl _ _) lw))
  (values B2 (EAS f1 _ B2 lw2) rc))

(def-adts
  ((Ng : ((Bool) a) ((Bool) b) -> Type)
    enum
    (many NgF : -> (Ng (BFalse) (BTrue)))
    (many NgT : -> (Ng (BTrue) (BFalse)))))

(def-fns _ $ (erased pb-fn : (erased (Nat) n) (erased (Bool) a b) (subterm erased (PB n a) p) (erased (PB n b) q) -> (erased (Eq (Bool) a b) e))
  (match erased p _
    ((PB0) (let-match erased q (PB0)) (Refl _ a))
    ((PBF n1 p1) (let-match erased q (PBF _ q1) (absurd (PBT _ q1) (pb-fn n1 _ _ p1 q1))) (Refl _ a))
    ((PBT n1 p1) (let-match erased q (PBT _ q1) (absurd (PBF _ q1) (pb-fn n1 _ _ p1 q1))) (Refl _ a))))

(def-fns _ $ (erased pb-s : (erased (Nat) n) (erased (Bool) a) (erased (PB n a) p) -> (erased (Bool) b) (erased (PB (Succ n) b) q) (erased (Ng a b) ng))
  (match erased a (((Bool) b) ((PB (Succ n) b) q) ((Ng a b) ng))
    ((BFalse) (values (BTrue) (PBT n p) (NgF)))
    ((BTrue) (values (BFalse) (PBF n p) (NgT)))))

(def-fns _ $ (erased pb-p : (erased (Nat) n) (erased (Bool) b) (erased (PB (Succ n) b) q) -> (erased (Bool) a) (erased (PB n a) p) (erased (Ng a b) ng))
  (match erased q _
    ((PBF _ p) (values (BTrue) p (NgT)))
    ((PBT _ p) (values (BFalse) p (NgF)))))

(def-fns _ $ (erased ng-fn : (erased (Bool) a b c) (erased (Ng a b) x) (erased (Ng a c) y) -> (erased (Eq (Bool) b c) e))
  (match erased x _ ((NgF) (let-match erased y (NgF)) (Refl _ b)) ((NgT) (let-match erased y (NgT)) (Refl _ b))))

(def-fns _ $ (erased double-pb : (erased (Nat) q n) (subterm erased (Double q n) d) -> (erased (PB n (BFalse)) p))
  (let-match erased d (DS q1 b d1) ((D0) (PB0)))
  (PBF (Succ b) (PBT b (double-pb q1 b d1))))

(def-adts
  ((RV : ((Nat) n) ((List (Nat)) rs) -> Type)
    enum
    (many RVN : -> (RV (Zero) (Nil (Nat))))
    (many RVE : (erased (Nat) q n) (erased (List (Nat)) rs) (erased (Double q n) d) (erased (RV q rs) r) -> (RV n (Cons (Nat) q rs)))
    (many RVO : (erased (Nat) q n) (erased (List (Nat)) rs) (erased (Double q n) d) (erased (RV q rs) r) -> (RV (Succ n) (Cons (Nat) (Succ q) rs)))))

(def-adts
  ((FO : ((List (Nat)) xs) ((List (Nat)) ys) -> Type)
    enum
    (many FOodd : (erased (Nat) y z) (erased (List (Nat)) zs) (erased (PB y (BTrue)) p) -> (FO (Cons (Nat) y (Cons (Nat) z zs)) (Cons (Nat) y (Cons (Nat) (Succ z) zs))))
    (many FOeven : (erased (Nat) x) (erased (List (Nat)) xs ys) (erased (PB (Succ x) (BFalse)) p) (erased (FO xs ys) f)
       -> (FO (Cons (Nat) (Succ x) xs) (Cons (Nat) (Succ x) ys)))))

(def-adts
  ((GSt : ((Nat) n) ((List (Nat)) r) ((List (Nat)) r2) -> Type)
    enum
    (many GSE : (erased (Nat) n q) (erased (List (Nat)) rs) (erased (PB n (BFalse)) p) -> (GSt n (Cons (Nat) q rs) (Cons (Nat) (Succ q) rs)))
    (many GSO : (erased (Nat) n) (erased (List (Nat)) r r2) (erased (PB n (BTrue)) p) (erased (FO r r2) f) -> (GSt n r r2))))

(def-fns _ $ (erased rv-down : (erased (Nat) n) (erased (List (Nat)) r2) (subterm erased (RV (Succ n) r2) rv) -> (erased (List (Nat)) r) (erased (RV n r) rv1) (erased (GSt n r r2) g))
  (let-match erased rv (RVE q _ rs d rr)
    ((RVO q _ rs d rr) (values (Cons (Nat) q rs) (RVE q n rs d rr) (GSE n q rs (double-pb q n d)))))
  (let-match erased d (DS q1 b d1))
  (let ((erased rs1) (erased rv1) (erased g1)) (rv-down q1 rs rr))
  (values (Cons (Nat) q rs1) (RVO q1 b rs1 d1 rv1)
    (GSO n _ _ (PBT b (double-pb q1 b d1))
      (match erased g1 (((FO (Cons (Nat) q rs1) (Cons (Nat) q rs)) f))
        ((GSE _ z zs p) (FOodd q z zs (PBT q1 p)))
        ((GSO _ _ _ p f) (FOeven q1 rs1 rs (PBF q1 p) f))))))

(def-adts
  ((SL : ((List (Nat)) xs) ((List (Nat)) ys) -> Type)
    enum
    (many SLN : -> (SL (Nil (Nat)) (Nil (Nat))))
    (many SLC : (erased (Nat) x y) (erased (List (Nat)) xs ys) (erased (SL xs ys) s) -> (SL (Cons (Nat) x xs) (Cons (Nat) y ys)))))

(def-fns _ $ (erased sl-tr : (erased (List (Nat)) xs ys zs) (subterm erased (SL xs ys) a) (erased (SL zs ys) b) -> (erased (SL xs zs) c))
  (let-match erased a (SLC x y xs1 ys1 a1) ((SLN) (let-match erased b (SLN)) (SLN)))
  (let-match erased b (SLC z _ zs1 _ b1))
  (SLC x z xs1 zs1 (sl-tr xs1 ys1 zs1 a1 b1)))

(def-fns _ $ (erased sl-refl : (subterm erased (List (Nat)) xs) -> (erased (SL xs xs) s))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (SLN)))
  (SLC x x xs1 xs1 (sl-refl xs1)))

(def-fns _ $ (erased fo-sl : (erased (List (Nat)) xs ys) (subterm erased (FO xs ys) f) -> (erased (SL xs ys) s))
  (match erased f _
    ((FOodd y z zs p) (SLC y y _ _ (SLC z (Succ z) zs zs (sl-refl zs))))
    ((FOeven x xs1 ys1 p f1) (SLC (Succ x) (Succ x) xs1 ys1 (fo-sl xs1 ys1 f1)))))

(def-fns _ $ (erased gst-sl : (erased (Nat) n) (erased (List (Nat)) r r2) (erased (GSt n r r2) g) -> (erased (SL r r2) s))
  (match erased g _
    ((GSE _ q rs p) (SLC q (Succ q) rs rs (sl-refl rs)))
    ((GSO _ _ _ p f) (fo-sl r r2 f))))

(def-fns _ $ (erased rv-fn : (erased (Nat) n) (erased (List (Nat)) r r2) (subterm erased (RV n r) a) (erased (RV n r2) b) (erased (SL r r2) s) -> (erased (Eq (List (Nat)) r r2) e))
  (match erased a _
    ((RVN) (let-match erased s (SLN)) (Refl _ r))
    ((RVE q _ rs d rr)
      (let-match erased s (SLC _ y _ ys s1))
      (let-match erased b (RVE q2 _ rs2 d2 rr2) (absurd RVN) (absurd (RVO q2 n2 rs2 d2 rr2) (double-parity q q2 n2 d d2)))
      (let-match erased (double-inj q q2 n d d2) (Refl _ _))
      (let-match erased (rv-fn q rs rs2 rr rr2 s1) (Refl _ _))
      (Refl _ r))
    ((RVO q n1 rs d rr)
      (let-match erased s (SLC _ y _ ys s1))
      (let-match erased b (RVO q2 _ rs2 d2 rr2) (absurd (RVE q2 _ rs2 d2 rr2) (double-parity q2 q n1 d2 d)))
      (let-match erased (double-inj q q2 n1 d d2) (Refl _ _))
      (let-match erased (rv-fn q rs rs2 rr rr2 s1) (Refl _ _))
      (Refl _ r))))

(def-adts
  ((UI : ((List (Nat)) xs) ((Nat) i) ((List (Nat)) ys) -> Type)
    enum
    (many UI0 : (erased (Nat) x) (erased (List (Nat)) xs) -> (UI (Cons (Nat) x xs) (Zero) (Cons (Nat) (Succ x) xs)))
    (many UIS : (erased (Nat) x i) (erased (List (Nat)) xs ys) (erased (UI xs i ys) u) -> (UI (Cons (Nat) x xs) (Succ i) (Cons (Nat) x ys)))))

(def-adts
  ((VP : ((List (Nat)) xs) ((List (Nat)) ys) -> Type)
    enum
    (many VPN : -> (VP (Nil (Nat)) (Nil (Nat))))
    (many VPC : (erased (Nat) c r) (erased (List (Nat)) cs rs) (erased (Bool) p) (erased (PB c p) pc) (erased (PB r p) pr) (erased (VP cs rs) v)
       -> (VP (Cons (Nat) c cs) (Cons (Nat) r rs)))))

(def-adts
  ((NZ : ((List (Nat)) xs) ((List (Nat)) ys) -> Type)
    enum
    (many NZN : -> (NZ (Nil (Nat)) (Nil (Nat))))
    (many NZ0 : (erased (Nat) c) (erased (List (Nat)) cs rs) (erased (NZ cs rs) v) -> (NZ (Cons (Nat) c cs) (Cons (Nat) (Zero) rs)))
    (many NZ1 : (erased (Nat) c r) (erased (List (Nat)) cs rs) (erased (NZ cs rs) v) -> (NZ (Cons (Nat) (Succ c) cs) (Cons (Nat) r rs)))))

(def-fns _ $ (erased fo-sw : (erased (List (Nat)) xs ys) (subterm erased (FO xs ys) f) -> (erased (Sw xs ys) w))
  (match erased f _
    ((FOodd y z zs p) (SwOdd y z zs p))
    ((FOeven x xs1 ys1 p f1) (SwEven x xs1 ys1 p (fo-sw xs1 ys1 f1)))))

(def-fns _ $ (erased lift-up : (erased (List (Nat)) r r2 c) (subterm erased (FO r r2) f) (erased (VP c r) vp) (erased (NZ c r) nz)
    -> (erased (List (Nat)) c2) (erased (Nat) i) (erased (FO c c2) fc) (erased (UI c i c2) u1) (erased (UI r i r2) u2))
  (match erased f _
    ((FOodd y z zs py)
      (let-match erased vp (VPC c0 r0 cs rs p pc pr vp1))
      (let-match erased (pb-fn y _ _ pr py) (Refl _ _))
      (let-match erased vp1 (VPC c1 _ cs1 _ _ _ _ _))
      (values (Cons (Nat) c0 (Cons (Nat) (Succ c1) cs1)) (Succ (Zero)) (FOodd c0 c1 cs1 pc) (UIS c0 _ _ _ (UI0 c1 cs1)) (UIS y _ _ _ (UI0 z zs))))
    ((FOeven x xs ys px f1)
      (let-match erased vp (VPC c0 r0 cs rs p pc pr vp1))
      (let-match erased (pb-fn (Succ x) _ _ pr px) (Refl _ _))
      (let-match erased nz (NZ1 c00 _ _ _ nz1))
      (let ((erased cs2) (erased i1) (erased fc1) (erased u3) (erased u4)) (lift-up xs ys cs f1 vp1 nz1))
      (values (Cons (Nat) c0 cs2) (Succ i1) (FOeven c00 cs cs2 pc fc1) (UIS c0 _ _ _ u3) (UIS (Succ x) _ _ _ u4)))))

(def-fns _ $ (erased lift-dn : (erased (List (Nat)) r r2 c) (subterm erased (FO r r2) f) (erased (VP c r2) vp) (erased (NZ c r2) nz)
    -> (erased (List (Nat)) c2) (erased (Nat) i) (erased (FO c c2) fc) (erased (UI c i c2) u1) (erased (UI r i r2) u2))
  (match erased f _
    ((FOodd y z zs py)
      (let-match erased vp (VPC c0 r0 cs rs p pc pr vp1))
      (let-match erased (pb-fn y _ _ pr py) (Refl _ _))
      (let-match erased vp1 (VPC c1 _ cs1 _ _ _ _ _))
      (values (Cons (Nat) c0 (Cons (Nat) (Succ c1) cs1)) (Succ (Zero)) (FOodd c0 c1 cs1 pc) (UIS c0 _ _ _ (UI0 c1 cs1)) (UIS y _ _ _ (UI0 z zs))))
    ((FOeven x xs ys px f1)
      (let-match erased vp (VPC c0 r0 cs rs p pc pr vp1))
      (let-match erased (pb-fn (Succ x) _ _ pr px) (Refl _ _))
      (let-match erased nz (NZ1 c00 _ _ _ nz1))
      (let ((erased cs2) (erased i1) (erased fc1) (erased u3) (erased u4)) (lift-dn xs ys cs f1 vp1 nz1))
      (values (Cons (Nat) c0 cs2) (Succ i1) (FOeven c00 cs cs2 pc fc1) (UIS c0 _ _ _ u3) (UIS (Succ x) _ _ _ u4)))))

(def-fns _ $ (erased vp-ui : (erased (List (Nat)) c c2 r r2) (erased (Nat) i) (subterm erased (UI c i c2) u1) (erased (UI r i r2) u2) (erased (VP c r) vp) -> (erased (VP c2 r2) vp2))
  (match erased u1 _
    ((UI0 _ _)
      (let-match erased vp (VPC c0 r0 cs rs p pc pr vp1))
      (let-match erased u2 (UI0 _ _))
      (let ((erased q) (erased pc2) (erased n1)) (pb-s c0 p pc))
      (let ((erased q2) (erased pr2) (erased n2)) (pb-s r0 p pr))
      (let-match erased (ng-fn p q q2 n1 n2) (Refl _ _))
      (VPC (Succ c0) (Succ r0) cs rs q pc2 pr2 vp1))
    ((UIS _ i1 _ cs2 u3)
      (let-match erased vp (VPC c0 r0 cs rs p pc pr vp1))
      (let-match erased u2 (UIS _ _ _ rs2 u4))
      (VPC c0 r0 cs2 rs2 p pc pr (vp-ui cs cs2 rs rs2 i1 u3 u4 vp1)))))

(def-fns _ $ (erased vp-ui-dn : (erased (List (Nat)) c c2 r r2) (erased (Nat) i) (subterm erased (UI c i c2) u1) (erased (UI r i r2) u2) (erased (VP c r2) vp) -> (erased (VP c2 r) vp2))
  (match erased u1 _
    ((UI0 _ _)
      (let-match erased vp (VPC c0 r0 cs rs p pc pr vp1))
      (let-match erased u2 (UI0 r1 _))
      (let ((erased q) (erased pc2) (erased n1)) (pb-s c0 p pc))
      (let ((erased q2) (erased pr2) (erased n2)) (pb-p r1 p pr))
      (let-match erased n1 (NgF) ((NgT) (let-match erased n2 (NgF)) (VPC (Succ c0) r1 cs rs q pc2 pr2 vp1)))
      (let-match erased n2 (NgT))
      (VPC (Succ c0) r1 cs rs q pc2 pr2 vp1))
    ((UIS _ i1 _ cs2 u3)
      (let-match erased vp (VPC c0 r0 cs rs p pc pr vp1))
      (let-match erased u2 (UIS _ _ rs1 _ u4))
      (VPC c0 r0 cs2 rs1 p pc pr (vp-ui-dn cs cs2 rs1 rs i1 u3 u4 vp1)))))

(def-fns _ $ (erased nz-ui : (erased (List (Nat)) c c2 r r2) (erased (Nat) i) (subterm erased (UI c i c2) u1) (erased (UI r i r2) u2) (erased (NZ c r) nz) -> (erased (NZ c2 r2) nz2))
  (match erased u1 _
    ((UI0 c0 cs)
      (let-match erased u2 (UI0 r0 rs))
      (let-match erased nz (NZ1 _ _ _ _ nz1) ((NZ0 _ _ _ nz1) (NZ1 c0 (Succ r0) cs rs nz1)))
      (NZ1 c0 (Succ r0) cs rs nz1))
    ((UIS c0 i1 cs cs2 u3)
      (let-match erased u2 (UIS r0 _ rs rs2 u4))
      (match erased nz _
        ((NZ0 _ _ _ nz1) (NZ0 c0 cs2 rs2 (nz-ui cs cs2 rs rs2 i1 u3 u4 nz1)))
        ((NZ1 c00 _ _ _ nz1) (NZ1 c00 r0 cs2 rs2 (nz-ui cs cs2 rs rs2 i1 u3 u4 nz1)))))))

(def-fns _ $ (erased nz-ui-dn : (erased (List (Nat)) c c2 r r2) (erased (Nat) i) (subterm erased (UI c i c2) u1) (erased (UI r i r2) u2) (erased (NZ c r2) nz) -> (erased (NZ c2 r) nz2))
  (match erased u1 _
    ((UI0 c0 cs)
      (let-match erased u2 (UI0 r0 rs))
      (let-match erased nz (NZ1 _ _ _ _ nz1))
      (NZ1 c0 r0 cs rs nz1))
    ((UIS c0 i1 cs cs2 u3)
      (let-match erased u2 (UIS r0 _ rs rs2 u4))
      (match erased nz _
        ((NZ0 _ _ _ nz1) (NZ0 c0 cs2 rs (nz-ui-dn cs cs2 rs rs2 i1 u3 u4 nz1)))
        ((NZ1 c00 _ _ _ nz1) (NZ1 c00 r0 cs2 rs (nz-ui-dn cs cs2 rs rs2 i1 u3 u4 nz1)))))))

(def-adts
  ((VA : ((List (Nat)) xs) ((List (Nat)) ys) ((List (Nat)) zs) -> Type)
    enum
    (many VAN : -> (VA (Nil (Nat)) (Nil (Nat)) (Nil (Nat))))
    (many VAC : (erased (Nat) x y z) (erased (List (Nat)) xs ys zs) (erased (Add x y z) a) (erased (VA xs ys zs) v)
       -> (VA (Cons (Nat) x xs) (Cons (Nat) y ys) (Cons (Nat) z zs)))))

(def-fns _ $ (erased va-ex : (erased (List (Nat)) xs ys) (subterm erased (SL xs ys) s) -> (erased (List (Nat)) zs) (erased (VA xs ys zs) v))
  (let-match erased s (SLC x y xs1 ys1 s1) ((SLN) (values (Nil (Nat)) (VAN))))
  (let ((erased z) (erased a)) (add-ex x y))
  (let ((erased zs1) (erased v1)) (va-ex xs1 ys1 s1))
  (values (Cons (Nat) z zs1) (VAC x y z xs1 ys1 zs1 a v1)))

(def-fns _ $ (erased va-fn : (erased (List (Nat)) xs ys zs zs2) (subterm erased (VA xs ys zs) v) (erased (VA xs ys zs2) w) -> (erased (Eq (List (Nat)) zs zs2) e))
  (let-match erased v (VAC x y z xs1 ys1 zs1 a v1) ((VAN) (let-match erased w (VAN)) (Refl _ zs)))
  (let-match erased w (VAC _ _ z2 _ _ zs3 a2 w1))
  (let-match erased (add-fn x y z z2 a a2) (Refl _ _))
  (let-match erased (va-fn xs1 ys1 zs1 zs3 v1 w1) (Refl _ _))
  (Refl _ zs))

(def-fns _ $ (erased va-comm : (erased (List (Nat)) xs ys zs) (subterm erased (VA xs ys zs) v) -> (erased (VA ys xs zs) w))
  (let-match erased v (VAC x y z xs1 ys1 zs1 a v1) ((VAN) (VAN)))
  (VAC y x z ys1 xs1 zs1 (add-comm x y z a) (va-comm xs1 ys1 zs1 v1)))

(def-fns _ $ (erased va-sl : (erased (List (Nat)) xs ys zs) (subterm erased (VA xs ys zs) v) -> (erased (SL xs zs) s))
  (let-match erased v (VAC x y z xs1 ys1 zs1 a v1) ((VAN) (SLN)))
  (SLC x z xs1 zs1 (va-sl xs1 ys1 zs1 v1)))

(def-fns _ $ (erased va-cancel : (erased (List (Nat)) xs xs2 ys zs) (subterm erased (VA xs ys zs) v) (erased (VA xs2 ys zs) w) -> (erased (Eq (List (Nat)) xs xs2) e))
  (let-match erased v (VAC x y z xs1 ys1 zs1 a v1) ((VAN) (let-match erased w (VAN)) (Refl _ xs)))
  (let-match erased w (VAC x2 _ _ xs3 _ _ a2 w1))
  (let-match erased (add-cancel y x x2 z (add-comm x y z a) (add-comm x2 y z a2)) (Refl _ _))
  (let-match erased (va-cancel xs1 xs3 ys1 zs1 v1 w1) (Refl _ _))
  (Refl _ xs))

(def-fns _ $ (erased add-assoc : (erased (Nat) a b c ab abc) (subterm erased (Add a b ab) p) (erased (Add ab c abc) q) -> (erased (Nat) bc) (erased (Add b c bc) r) (erased (Add a bc abc) s))
  (let-match erased p (AddSucc a1 _ ab1 p1) ((AddZero _) (values abc q (AddZero abc))))
  (let-match erased q (AddSucc _ _ abc1 q1))
  (let ((erased bc) (erased r) (erased s)) (add-assoc a1 b c ab1 abc1 p1 q1))
  (values bc r (AddSucc a1 bc abc1 s)))

(def-fns _ $ (erased va-assoc : (erased (List (Nat)) xs ys zs xy xyz) (subterm erased (VA xs ys xy) v) (erased (VA xy zs xyz) w)
    -> (erased (List (Nat)) yz) (erased (VA ys zs yz) v2) (erased (VA xs yz xyz) w2))
  (let-match erased v (VAC x y s xs1 ys1 xy1 a v1) ((VAN) (let-match erased w (VAN)) (values (Nil (Nat)) (VAN) (VAN))))
  (let-match erased w (VAC _ z t _ zs1 xyz1 b w1))
  (let ((erased u) (erased c) (erased d)) (add-assoc x y z s t a b))
  (let ((erased yz1) (erased v3) (erased w3)) (va-assoc xs1 ys1 zs1 xy1 xyz1 v1 w1))
  (values (Cons (Nat) u yz1) (VAC y z u ys1 zs1 yz1 c v3) (VAC x u t xs1 yz1 xyz1 d w3)))

(def-fns _ $ (erased va-ui-l : (erased (List (Nat)) x x2 y z) (erased (Nat) i) (subterm erased (UI x i x2) u) (erased (VA x y z) v)
    -> (erased (List (Nat)) z2) (erased (UI z i z2) u2) (erased (VA x2 y z2) v2))
  (match erased u _
    ((UI0 a xs)
      (let-match erased v (VAC _ b c _ ys zs ad v1))
      (values (Cons (Nat) (Succ c) zs) (UI0 c zs) (VAC (Succ a) b (Succ c) xs ys zs (AddSucc a b c ad) v1)))
    ((UIS a i1 xs xs2 u1)
      (let-match erased v (VAC _ b c _ ys zs ad v1))
      (let ((erased zs2) (erased u3) (erased v3)) (va-ui-l xs xs2 ys zs i1 u1 v1))
      (values (Cons (Nat) c zs2) (UIS c i1 zs zs2 u3) (VAC a b c xs2 ys zs2 ad v3)))))

(def-fns _ $ (erased va-ui-r : (erased (List (Nat)) x y y2 z z2) (erased (Nat) i) (subterm erased (UI y i y2) u) (erased (UI z i z2) u2) (erased (VA x y z) v)
    -> (erased (VA x y2 z2) v2))
  (match erased u _
    ((UI0 b ys)
      (let-match erased u2 (UI0 c zs))
      (let-match erased v (VAC a _ _ xs _ _ ad v1))
      (VAC a (Succ b) (Succ c) xs ys zs (add-succ-right a b c ad) v1))
    ((UIS b i1 ys ys2 u1)
      (let-match erased u2 (UIS c _ zs zs2 u3))
      (let-match erased v (VAC a _ _ xs _ _ ad v1))
      (VAC a b c xs ys2 zs2 ad (va-ui-r xs ys ys2 zs zs2 i1 u1 u3 v1)))))

(def-fns _ $ (erased va-ui-sw : (erased (List (Nat)) x x2 y y2 z) (erased (Nat) i) (subterm erased (UI x i x2) u) (erased (UI y i y2) u2) (erased (VA x2 y z) v)
    -> (erased (VA x y2 z) v2))
  (match erased u _
    ((UI0 a xs)
      (let-match erased u2 (UI0 b ys))
      (let-match erased v (VAC _ _ c _ _ zs ad v1))
      (VAC a (Succ b) c xs ys zs (add-unshift a b c ad) v1))
    ((UIS a i1 xs xs2 u1)
      (let-match erased u2 (UIS b _ ys ys2 u3))
      (let-match erased v (VAC _ _ c _ _ zs ad v1))
      (VAC a b c xs ys2 zs ad (va-ui-sw xs xs2 ys ys2 zs i1 u1 u3 v1)))))

(def-fns _ $ (erased ng-ng : (erased (Bool) a b c) (erased (Ng a b) x) (erased (Ng b c) y) -> (erased (Eq (Bool) a c) e))
  (match erased x _ ((NgF) (let-match erased y (NgT)) (Refl _ a)) ((NgT) (let-match erased y (NgF)) (Refl _ a))))

(def-fns _ $ (erased vp-sl : (erased (List (Nat)) xs ys) (subterm erased (VP xs ys) v) -> (erased (SL xs ys) s))
  (let-match erased v (VPC x y xs1 ys1 _ _ _ v1) ((VPN) (SLN)))
  (SLC x y xs1 ys1 (vp-sl xs1 ys1 v1)))

(def-fns _ $ (erased ng-sw : (erased (Bool) a a2 b b2) (erased (Ng a a2) x) (erased (Ng b b2) y) (erased (Ng a2 b2) z) -> (erased (Ng a b) r))
  (match erased z _ ((NgF) (let-match erased x (NgT)) (let-match erased y (NgF)) (NgT)) ((NgT) (let-match erased x (NgF)) (let-match erased y (NgT)) (NgF))))

(def-fns _ $ (erased sl-sym : (erased (List (Nat)) xs ys) (subterm erased (SL xs ys) s) -> (erased (SL ys xs) r))
  (let-match erased s (SLC x y xs1 ys1 s1) ((SLN) (SLN)))
  (SLC y x ys1 xs1 (sl-sym xs1 ys1 s1)))

(def-fns _ $ (erased gstep-up : (erased (Nat) m f) (erased (List (Nat)) c r r2) (erased (List (Bool)) B) (erased (GSt m r r2) gs) (erased (Bool) p)
    (erased (PB (Succ f) p) pf) (erased (PB m p) pm) (erased (VP c r) vp) (erased (NZ c r) nz) (erased (EncA (Succ f) c B) ea)
    -> (erased (List (Nat)) c2) (erased (Nat) i) (erased (UI c i c2) u1) (erased (UI r i r2) u2) (erased (List (Bool)) B2) (erased (EncA f c2 B2) ea2)
    (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) (BTrue)) rc))
  (match erased gs _
    ((GSE _ q rs pq)
      (let-match erased (pb-fn m _ _ pm pq) (Refl _ _))
      (let-match erased pf (PBF _ pf1))
      (let-match erased vp (VPC c0 _ cs _ _ _ _ _))
      (let ((erased B2) (erased ea2) (erased rc)) (mstep-e f c0 cs B pf1 ea))
      (values (Cons (Nat) (Succ c0) cs) (Zero) (UI0 c0 cs) (UI0 q rs) B2 ea2 rc))
    ((GSO _ _ _ pq fo)
      (let-match erased (pb-fn m _ _ pm pq) (Refl _ _))
      (let-match erased pf (PBT _ pf1))
      (let ((erased c2) (erased i) (erased fc) (erased u1) (erased u2)) (lift-up r r2 c fo vp nz))
      (let ((erased B2) (erased ea2) (erased rc)) (mstep-o f c c2 B pf1 (fo-sw c c2 fc) ea))
      (values c2 i u1 u2 B2 ea2 rc))))

(def-fns _ $ (erased gstep-dn : (erased (Nat) m f) (erased (List (Nat)) c r r2) (erased (List (Bool)) B) (erased (GSt m r r2) gs) (erased (Bool) p q)
    (erased (PB (Succ f) p) pf) (erased (PB (Succ m) q) pm) (erased (Ng p q) ng) (erased (VP c r2) vp) (erased (NZ c r2) nz) (erased (EncA (Succ f) c B) ea)
    -> (erased (List (Nat)) c2) (erased (Nat) i) (erased (UI c i c2) u1) (erased (UI r i r2) u2) (erased (List (Bool)) B2) (erased (EncA f c2 B2) ea2)
    (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) (BTrue)) rc))
  (match erased gs _
    ((GSE _ q0 rs pq)
      (let-match erased (pb-fn (Succ m) _ _ pm (PBT m pq)) (Refl _ _))
      (let-match erased ng (NgF))
      (let-match erased pf (PBF _ pf1))
      (let-match erased vp (VPC c0 _ cs _ _ _ _ _))
      (let ((erased B2) (erased ea2) (erased rc)) (mstep-e f c0 cs B pf1 ea))
      (values (Cons (Nat) (Succ c0) cs) (Zero) (UI0 c0 cs) (UI0 q0 rs) B2 ea2 rc))
    ((GSO _ _ _ pq fo)
      (let-match erased (pb-fn (Succ m) _ _ pm (PBF m pq)) (Refl _ _))
      (let-match erased ng (NgT))
      (let-match erased pf (PBT _ pf1))
      (let ((erased c2) (erased i) (erased fc) (erased u1) (erased u2)) (lift-dn r r2 c fo vp nz))
      (let ((erased B2) (erased ea2) (erased rc)) (mstep-o f c c2 B pf1 (fo-sw c c2 fc) ea))
      (values c2 i u1 u2 B2 ea2 rc))))

(def-fns _ $ (erased up-run : (erased (Nat) n t m f f2) (erased (List (Nat)) c rn rm) (erased (List (Bool)) B)
    (subterm erased (Add t n m) am) (erased (Add t f2 f) af) (erased (RV n rn) rvn) (erased (RV m rm) rvm) (erased (SL rn rm) sl)
    (erased (Bool) p) (erased (PB f p) pf) (erased (PB n p) pn) (erased (VP c rn) vp) (erased (NZ c rn) nz) (erased (EncA f c B) ea)
    -> (erased (List (Nat)) c2 w) (erased (List (Bool)) B2) (erased (Bool) p2) (erased (PB f2 p2) pf2) (erased (PB m p2) pm2)
    (erased (VP c2 rm) vp2) (erased (NZ c2 rm) nz2) (erased (EncA f2 c2 B2) ea2) (erased (VA c2 rn w) va1) (erased (VA c rm w) va2)
    (erased (Bool) g) (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) g) rc))
  (let-match erased am (AddSucc t1 _ m1 am1)
    ((AddZero _)
      (let-match erased af (AddZero _))
      (let-match erased (rv-fn n rn rm rvn rvm sl) (Refl _ _))
      (let ((erased w) (erased va)) (va-ex c rn (vp-sl c rn vp)))
      (values c w B p pf pn vp nz ea va va (BFalse) (reach-refl p17 _))))
  (let ((erased r1) (erased rv1) (erased gs)) (rv-down m1 rm rvm))
  (let ((erased c1) (erased w1) (erased B1) (erased p1) (erased pf1) (erased pm1) (erased vp1) (erased nz1) (erased ea1) (erased va1) (erased va2) (erased g1) (erased rc1))
    (up-run n t1 m1 f (Succ f2) c rn r1 B am1 (add-unshift t1 f2 f af) rvn rv1 (sl-tr rn rm r1 sl (gst-sl m1 r1 rm gs)) p pf pn vp nz ea))
  (let ((erased c2) (erased i) (erased u1) (erased u2) (erased B2) (erased ea2) (erased rc2)) (gstep-up m1 f2 c1 r1 rm B1 gs p1 pf1 pm1 vp1 nz1 ea1))
  (let ((erased w2) (erased u3) (erased va3)) (va-ui-l c1 c2 rn w1 i u1 va1))
  (let ((erased p2) (erased pm2) (erased ng)) (pb-s m1 p1 pm1))
  (let ((erased p3) (erased pf3) (erased ng2)) (pb-p f2 p1 pf1))
  (let-match erased (ng-ng p3 p1 p2 ng2 ng) (Refl _ _))
  (let ((erased g) (erased rc)) (rcat _ _ _ _ _ rc1 rc2))
  (values c2 w2 B2 p2 pf3 pm2 (vp-ui c1 c2 r1 rm i u1 u2 vp1) (nz-ui c1 c2 r1 rm i u1 u2 nz1) ea2 va3 (va-ui-r c r1 rm w1 w2 i u2 u3 va2) g rc))

(def-fns _ $ (erased dn-run : (erased (Nat) n t m f f2) (erased (List (Nat)) c rn) (erased (List (Bool)) B)
    (subterm erased (Add t m n) am) (erased (Add t f2 f) af) (erased (RV n rn) rvn)
    (erased (Bool) p q) (erased (PB f p) pf) (erased (PB n q) pn) (erased (Ng p q) ng) (erased (VP c rn) vp) (erased (NZ c rn) nz) (erased (EncA f c B) ea)
    -> (erased (List (Nat)) c2 rm w) (erased (RV m rm) rvm) (erased (SL rn rm) sl) (erased (List (Bool)) B2) (erased (Bool) p2 q2) (erased (PB f2 p2) pf2) (erased (PB m q2) pm2) (erased (Ng p2 q2) ng2)
    (erased (VP c2 rm) vp2) (erased (NZ c2 rm) nz2) (erased (EncA f2 c2 B2) ea2) (erased (VA c2 rm w) va1) (erased (VA c rn w) va2)
    (erased (Bool) g) (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) g) rc))
  (let-match erased am (AddSucc t1 _ n1 am1)
    ((AddZero _)
      (let-match erased af (AddZero _))
      (let ((erased w) (erased va)) (va-ex c rn (vp-sl c rn vp)))
      (values c rn w rvn (sl-refl rn) B p q pf pn ng vp nz ea va va (BFalse) (reach-refl p17 _))))
  (let-match erased af (AddSucc _ _ f1 af1))
  (let ((erased r1) (erased rv1) (erased gs)) (rv-down n1 rn rvn))
  (let ((erased c1) (erased i) (erased u1) (erased u2) (erased B1) (erased ea1) (erased rc1)) (gstep-dn n1 f1 c r1 rn B gs p q pf pn ng vp nz ea))
  (let ((erased p1) (erased pf1) (erased ngp)) (pb-p f1 p pf))
  (let ((erased q1) (erased pn1) (erased ngq)) (pb-p n1 q pn))
  (let ((erased c2) (erased rm) (erased w) (erased rvm) (erased sl) (erased B2) (erased p2) (erased q2) (erased pf2) (erased pm2) (erased ng2) (erased vp2) (erased nz2) (erased ea2) (erased va1) (erased va2) (erased g2) (erased rc2))
    (dn-run n1 t1 m f1 f2 c1 r1 B1 am1 af1 rv1 p1 q1 pf1 pn1 (ng-sw p1 p q1 q ngp ngq ng) (vp-ui-dn c c1 r1 rn i u1 u2 vp) (nz-ui-dn c c1 r1 rn i u1 u2 nz) ea1))
  (let ((erased g) (erased rc)) (rcat _ _ _ _ _ rc1 rc2))
  (values c2 rm w rvm (sl-tr rn r1 rm (sl-sym r1 rn (gst-sl n1 r1 rn gs)) (sl-sym r1 rm sl)) B2 p2 q2 pf2 pm2 ng2 vp2 nz2 ea2 va1 (va-ui-sw c c1 r1 rn w i u1 u2 va2) g rc))

(def-adts
  ((TV : ((List (Nat)) rs) -> Type)
    enum
    (many TVL : -> (TV (Cons (Nat) (Succ (Zero)) (Nil (Nat)))))
    (many TVC : (erased (Nat) e) (erased (List (Nat)) rs) (erased (PB e (BFalse)) p) (erased (TV rs) t) -> (TV (Cons (Nat) e rs)))))

(def-adts
  ((P2 : ((List (Nat)) xs) ((List (Nat)) ys) -> Type)
    enum
    (many P2N : -> (P2 (Nil (Nat)) (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat))))))
    (many P2C : (erased (Nat) x) (erased (List (Nat)) xs ys) (erased (P2 xs ys) p) -> (P2 (Cons (Nat) x xs) (Cons (Nat) x ys)))))

(def-adts
  ((ZC : ((List (Nat)) cs) -> Type)
    enum
    (many ZCL : (erased (Nat) y) (erased (PB y (BFalse)) p) -> (ZC (Cons (Nat) y (Nil (Nat)))))
    (many ZCC : (erased (Nat) x) (erased (List (Nat)) xs) (erased (PB (Succ x) (BFalse)) p) (erased (ZC xs) z) -> (ZC (Cons (Nat) (Succ x) xs)))))

(def-adts
  ((ZE : ((List (Nat)) cs) ((List (Nat)) zs) -> Type)
    enum
    (many ZEL : (erased (Nat) y) -> (ZE (Cons (Nat) y (Nil (Nat))) (Cons (Nat) (Succ y) (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat)))))))
    (many ZEC : (erased (Nat) x) (erased (List (Nat)) xs ys) (erased (ZE xs ys) z) -> (ZE (Cons (Nat) x xs) (Cons (Nat) x ys)))))

(def-fns _ $ (erased ze-sw : (erased (List (Nat)) cs zs) (subterm erased (ZE cs zs) ze) (erased (ZC cs) zc) -> (erased (Sw cs zs) w))
  (match erased ze _
    ((ZEL y) (let-match erased zc (ZCL _ p) (absurd (ZCC _ _ _ z) z)) (SwLast y p))
    ((ZEC x xs ys ze1)
      (let-match erased zc (ZCC x1 _ p zc1) (absurd (ZCL _ _) ze1))
      (SwEven x1 xs ys p (ze-sw xs ys ze1 zc1)))))

(def-fns _ $ (erased ze-vp : (erased (List (Nat)) cs zs rs R0) (subterm erased (ZE cs zs) ze) (erased (ZC cs) zc) (erased (SL cs rs) sl) (erased (TV rs) tv) (erased (P2 rs R0) p2)
    -> (erased (VP zs R0) vp) (erased (NZ zs R0) nz))
  (match erased ze _
    ((ZEL y)
      (let-match erased zc (ZCL _ p) (absurd (ZCC _ _ _ z) z))
      (let-match erased sl (SLC _ e _ rs1 sl1))
      (let-match erased sl1 (SLN))
      (let-match erased tv (TVL) (absurd (TVC _ _ _ t) t))
      (let-match erased p2 (P2C _ _ _ p21))
      (let-match erased p21 (P2N))
      (values (VPC (Succ y) (Succ (Zero)) _ _ (BTrue) (PBT y p) (PBT (Zero) (PB0)) (VPC (Zero) (Zero) _ _ (BFalse) (PB0) (PB0) (VPC (Zero) (Zero) _ _ (BFalse) (PB0) (PB0) (VPN))))
        (NZ1 y _ _ _ (NZ0 (Zero) _ _ (NZ0 (Zero) _ _ (NZN))))))
    ((ZEC x xs ys ze1)
      (let-match erased zc (ZCC x1 _ p zc1) (absurd (ZCL _ _) ze1))
      (let-match erased sl (SLC _ e _ rs1 sl1))
      (let-match erased tv (TVC _ _ pe tv1) (absurd (TVL) (let-match erased sl1 (SLN)) ze1))
      (let-match erased p2 (P2C _ _ R1 p21))
      (let ((erased vp) (erased nz)) (ze-vp xs ys rs1 R1 ze1 zc1 sl1 tv1 p21))
      (values (VPC x e ys R1 (BFalse) p pe vp) (NZ1 x1 e ys R1 nz)))))

(def-fns _ $ (erased add-cancel-r : (erased (Nat) x y a z) (erased (Add x a z) p) (erased (Add y a z) q) -> (erased (Eq (Nat) x y) e))
  (add-cancel a x y z (add-comm x a z p) (add-comm y a z q)))

(def-fns _ $ (erased rv-pad : (erased (Nat) n) (erased (List (Nat)) rs rs2) (subterm erased (P2 rs rs2) p) (erased (RV n rs) rv) -> (erased (RV n rs2) rv2))
  (match erased p _
    ((P2N) (let-match erased rv (RVN)) (RVE (Zero) (Zero) _ (D0) (RVE (Zero) (Zero) _ (D0) (RVN))))
    ((P2C x xs ys p1)
      (match erased rv _
        ((RVE q _ _ d r) (RVE q n ys d (rv-pad q xs ys p1 r)))
        ((RVO q n1 _ d r) (RVO q n1 ys d (rv-pad q xs ys p1 r)))))))

(def-adts
  ((TopN : ((Nat) n) ((List (Nat)) rs) -> Type)
    enum
    (many TN0 : -> (TopN (Zero) (Nil (Nat))))
    (many TNS : (erased (Nat) q n) (erased (List (Nat)) rs) (erased (TopN q rs) t) (erased (Double q n) d) -> (TopN (Succ n) (Cons (Nat) (Succ q) rs)))))

(def-fns _ $ (erased topn-rv : (erased (Nat) n) (erased (List (Nat)) rs) (subterm erased (TopN n rs) t) -> (erased (RV n rs) rv))
  (let-match erased t (TNS q n1 rs1 t1 d) ((TN0) (RVN)))
  (RVO q n1 rs1 d (topn-rv q rs1 t1)))

(def-fns _ $ (erased topn-tv : (erased (Nat) n r) (erased (List (Nat)) rs) (subterm erased (TopN n (Cons (Nat) r rs)) t) -> (erased (TV (Cons (Nat) r rs)) tv))
  (let-match erased t (TNS q n1 _ t1 d))
  (let-match erased t1 (TNS q2 n2 rs2 t2 d2) ((TN0) (let-match erased d (D0)) (TVL)))
  (TVC (Succ q) rs (PBF q (PBT n2 (double-pb q2 n2 d2))) (topn-tv q (Succ q2) rs2 t1)))

(def-fns _ $ (erased topn-fn : (erased (Nat) a b) (erased (List (Nat)) x y) (subterm erased (TopN a x) t) (erased (TopN b y) u) (erased (SL x y) s) -> (erased (Eq (Nat) a b) e))
  (let-match erased t (TNS q n x1 t1 d) ((TN0) (let-match erased s (SLN)) (let-match erased u (TN0)) (Refl _ a)))
  (let-match erased s (SLC _ _ _ y1 s1))
  (let-match erased u (TNS q2 n2 _ u1 d2))
  (let-match erased (topn-fn q q2 x1 y1 t1 u1 s1) (Refl _ _))
  (let-match erased (double-fn q n n2 d d2) (Refl _ _))
  (Refl _ a))

(def-fns _ $ (erased add-assoc-r : (erased (Nat) a b c bc abc) (subterm erased (Add a bc abc) p) (erased (Add b c bc) q) -> (erased (Nat) ab) (erased (Add a b ab) r) (erased (Add ab c abc) s))
  (let-match erased p (AddSucc a1 _ abc1 p1) ((AddZero _) (values b (AddZero b) q)))
  (let ((erased ab) (erased r) (erased s)) (add-assoc-r a1 b c bc abc1 p1 q))
  (values (Succ ab) (AddSucc a1 b ab r) (AddSucc ab c abc1 s)))

(def-fns _ $ (erased add-rot : (erased (Nat) u v w uv s) (erased (Add u v uv) p) (erased (Add uv w s) q) -> (erased (Nat) uw) (erased (Add u w uw) r) (erased (Add uw v s) t))
  (let ((erased vw) (erased p1) (erased q1)) (add-assoc u v w uv s p q))
  (add-assoc-r u w v vw s q1 (add-comm v w vw p1)))

(def-fns _ $ (erased alg0 : (erased (Nat) o a a2 t c x w n) (erased (Add o a2 t) p1) (erased (Add a a a2) p2) (erased (Add c a t) p3) (erased (Add x a w) p4) (erased (Add c n w) p5)
    -> (erased (Add o n x) r))
  (let ((erased oa) (erased q1) (erased q2)) (add-assoc-r o a a a2 t p1 p2))
  (let-match erased (add-cancel-r oa c a t q2 p3) (Refl _ _))
  (let ((erased an) (erased q3) (erased q4)) (add-assoc o a n c w q1 p5))
  (let ((erased on) (erased q5) (erased q6)) (add-assoc-r o n a an w q4 (add-comm a n an q3)))
  (let-match erased (add-cancel-r x on a w p4 q6) (Refl _ _))
  q5)

(def-fns _ $ (erased alg1 : (erased (Nat) o a a2 q t r r2 c x w) (erased (Add o a2 q) p1) (erased (Add t r2 q) p2) (erased (Add a a a2) p3) (erased (Add r r r2) p4)
    (erased (Add c a t) p5) (erased (Add x a w) p6) (erased (Add c r w) p7) -> (erased (Add x r o) res))
  (let ((erased xr) (erased q1)) (add-ex x r))
  (let ((erased s1) (erased q2)) (add-ex xr a))
  (let ((erased uw) (erased q3) (erased q4)) (add-rot x r a xr s1 q1 q2))
  (let-match erased (add-fn x a uw w q3 p6) (Refl _ _))
  (let ((erased rr) (erased q5) (erased q6)) (add-assoc c r r w s1 p7 q4))
  (let-match erased (add-fn r r rr r2 q5 p4) (Refl _ _))
  (let ((erased s2) (erased q7)) (add-ex s1 a))
  (let ((erased cw) (erased q8) (erased q9)) (add-rot c r2 a s1 s2 q6 q7))
  (let-match erased (add-fn c a cw t q8 p5) (Refl _ _))
  (let-match erased (add-fn t r2 s2 q q9 p2) (Refl _ _))
  (let ((erased aa) (erased q10) (erased q11)) (add-assoc xr a a s1 q q2 q7))
  (let-match erased (add-fn a a aa a2 q10 p3) (Refl _ _))
  (let-match erased (add-cancel-r o xr a2 q p1 q11) (Refl _ _))
  q1)

(def-fns _ $ (erased valg1 : (erased (List (Nat)) o a a2 q t r r2 c x w) (subterm erased (VA o a2 q) p1) (erased (VA t r2 q) p2) (erased (VA a a a2) p3) (erased (VA r r r2) p4)
    (erased (VA c a t) p5) (erased (VA x a w) p6) (erased (VA c r w) p7) -> (erased (VA x r o) res))
  (let-match erased p1 (VAC o0 a20 q0 os a2s qs e1 v1) ((VAN)
    (let-match erased p3 (VAN)) (let-match erased p6 (VAN)) (let-match erased p7 (VAN)) (VAN)))
  (let-match erased p2 (VAC t0 r20 _ ts r2s _ e2 v2))
  (let-match erased p3 (VAC a0 _ _ as _ _ e3 v3))
  (let-match erased p4 (VAC r0 _ _ rs _ _ e4 v4))
  (let-match erased p5 (VAC c0 _ _ cs _ _ e5 v5))
  (let-match erased p6 (VAC x0 _ w0 xs _ ws e6 v6))
  (let-match erased p7 (VAC _ _ _ _ _ _ e7 v7))
  (VAC x0 r0 o0 xs rs os (alg1 o0 a0 a20 q0 t0 r0 r20 c0 x0 w0 e1 e2 e3 e4 e5 e6 e7) (valg1 os as a2s qs ts rs r2s cs xs ws v1 v2 v3 v4 v5 v6 v7)))

(def-fns _ $ (erased va-zero : (erased (Nat) n) (erased (List (Nat)) z c w) (subterm erased (RV n z) rv) (erased (Eq (Nat) n (Zero)) e) (erased (VA c z w) v) -> (erased (Eq (List (Nat)) c w) r))
  (let-match erased e (Refl _ _))
  (match erased rv _
    ((RVN) (let-match erased v (VAN)) (Refl _ c))
    ((RVE q _ rs d r)
      (let-match erased d (D0))
      (let-match erased v (VAC c0 _ w0 cs _ ws a v1))
      (let-match erased (add-fn c0 (Zero) w0 c0 a (add-zero-right c0)) (Refl _ _))
      (let-match erased (va-zero (Zero) rs cs ws r (Refl _ _) v1) (Refl _ _))
      (Refl _ c))))

(def-adts
  ((X3 : ((Bool) a) ((Bool) b) ((Bool) c) -> Type)
    enum
    (many XFF : -> (X3 (BFalse) (BFalse) (BFalse)))
    (many XFT : -> (X3 (BFalse) (BTrue) (BTrue)))
    (many XTF : -> (X3 (BTrue) (BFalse) (BTrue)))
    (many XTT : -> (X3 (BTrue) (BTrue) (BFalse)))))

(def-fns _ $ (erased pb-ex : (subterm erased (Nat) n) -> (erased (Bool) b) (erased (PB n b) p))
  (let-match erased n (Succ n1) ((Zero) (values (BFalse) (PB0))))
  (let ((erased b1) (erased p1)) (pb-ex n1))
  (let ((erased b) (erased p) (erased _)) (pb-s n1 b1 p1))
  (values b p))

(def-fns _ $ (erased par-add : (erased (Nat) a b c) (erased (Bool) pa pb) (subterm erased (Add a b c) s) (erased (PB a pa) qa) (erased (PB b pb) qb)
    -> (erased (Bool) pc) (erased (PB c pc) qc) (erased (X3 pa pb pc) x))
  (let-match erased s (AddSucc a1 _ c1 s1)
    ((AddZero _) (let-match erased qa (PB0)) (values pb qb (match erased pb (((X3 (BFalse) pb pb) x)) ((BFalse) (XFF)) ((BTrue) (XFT))))))
  (let ((erased pa1) (erased qa1) (erased n1)) (pb-p a1 pa qa))
  (let ((erased pc1) (erased qc1) (erased x1)) (par-add a1 b c1 pa1 pb s1 qa1 qb))
  (let ((erased pc) (erased qc) (erased n2)) (pb-s c1 pc1 qc1))
  (values pc qc
    (match erased x1 (((X3 pa pb pc) x))
      ((XFF) (let-match erased n1 (NgF)) (let-match erased n2 (NgF)) (XTF))
      ((XFT) (let-match erased n1 (NgF)) (let-match erased n2 (NgT)) (XTT))
      ((XTF) (let-match erased n1 (NgT)) (let-match erased n2 (NgT)) (XFF))
      ((XTT) (let-match erased n1 (NgT)) (let-match erased n2 (NgF)) (XFT)))))

(def-fns _ $ (erased par-sub : (erased (Nat) a b c) (erased (Bool) pb) (erased (Add a b c) s) (erased (PB b pb) qb) (erased (PB c (BFalse)) qc) -> (erased (PB a pb) qa))
  (let ((erased pa) (erased qa)) (pb-ex a))
  (let ((erased pc) (erased qc2) (erased x)) (par-add a b c pa pb s qa qb))
  (let-match erased (pb-fn c _ _ qc qc2) (Refl _ _))
  (match erased x _ ((XFF) qa) ((XTT) qa)))

(def-fns _ $ (erased ng-flip : (erased (Bool) a b) (erased (Ng a b) x) -> (erased (Ng b a) y))
  (match erased x _ ((NgF) (NgT)) ((NgT) (NgF))))

(def-adts
  ((Cy : ((Nat) N0) ((List (Nat)) X) ((List (Nat)) O) ((Nat) N2) ((Nat) N4) -> Type)
    enum
    (many MkCy : (erased (Nat) N0 x0 r00 r01 t00 N1h N2 N4) (erased (List (Nat)) c z0 rs rr T0t A R4 A2 R42 Q O)
       (erased (TopN N0 rs) tn) (erased (P2 rs (Cons (Nat) r00 (Cons (Nat) r01 rr))) p2) (erased (SL c rs) slc)
       (erased (PB x0 (BFalse)) px) (erased (ZC c) zc) (erased (ZE c z0) ze)
       (erased (VA z0 (Cons (Nat) r00 (Cons (Nat) r01 rr)) (Cons (Nat) t00 T0t)) vt) (erased (PB t00 (BFalse)) pt)
       (erased (Add x0 (Succ N1h) N0) a1) (erased (Double N2 N1h) d2) (erased (RV N2 A) rva) (erased (SL A (Cons (Nat) r01 rr)) sla)
       (erased (Double N4 t00) d4) (erased (RV N4 R4) rv4) (erased (SL rr R4) slr)
       (erased (VA A A A2) aa) (erased (VA R4 R4 R42) rr2) (erased (VA O A2 Q) vo) (erased (VA T0t (Cons (Nat) (Zero) R42) Q) vq)
       -> (Cy N0 (Cons (Nat) x0 c) O N2 N4))))

(def-fns _ $ (erased nz-tl : (erased (Nat) c r) (erased (List (Nat)) cs rs) (erased (NZ (Cons (Nat) c cs) (Cons (Nat) r rs)) nz) -> (erased (NZ cs rs) t))
  (match erased nz _ ((NZ0 _ _ _ t) t) ((NZ1 _ _ _ _ t) t)))

(def-fns _ $ (erased cycle : (erased (Nat) N0 x0 M2 M4) (erased (List (Nat)) c O) (erased (List (Bool)) B) (erased (Cy N0 (Cons (Nat) x0 c) O M2 M4) cy) (erased (EncA (Succ x0) c B) ea)
    -> (erased (List (Bool)) B2) (erased (Lw O B2) lw) (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) (BTrue)) rc))
  (let-match erased cy (MkCy _ _ r00 r01 t00 N1h N2 N4 _ z0 rs rr T0t A R4 A2 R42 Q _ tn p2 slc px zc ze vt pt a1 d2 rva sla d4 rv4 slr aa rr2 vo vq))
  (let-match erased slc (SLC _ rs0 _ rs1 _) (absurd (SLN) zc))
  (let-match erased tn (TNS q0 n0 _ tn1 d0))
  (let ((erased tv)) (topn-tv N0 rs0 rs1 tn))
  (let ((erased rv0)) (rv-pad N0 rs _ p2 (topn-rv N0 rs tn)))
  (let ((erased pn0)) (PBT n0 (double-pb q0 n0 d0)))
  (let ((erased B1) (erased ea1) (erased rcz)) (mstep-o x0 c z0 B px (ze-sw c z0 ze zc) ea))
  (let ((erased vp0) (erased nz0)) (ze-vp c z0 rs _ ze zc slc tv p2))
  (let ((erased c1) (erased R1) (erased W) (erased rv1) (erased sl01) (erased B2) (erased p2a) (erased q2a) (erased pf2) (erased pm2) (erased ng2) (erased vp1) (erased nz1) (erased ea2) (erased va1) (erased va2) (erased g1) (erased rc1))
    (dn-run N0 x0 (Succ N1h) x0 (Zero) z0 _ B1 a1 (add-zero-right x0) rv0 (BFalse) (BTrue) px pn0 (NgF) vp0 nz0 ea1))
  (let-match erased (va-fn z0 _ W _ va2 vt) (Refl _ _))
  (let-match erased rv1 (RVO q1 _ A1 d1 rva1) (absurd (RVE q1 _ A1 d1 rva1) (double-parity q1 N2 N1h d1 d2)))
  (let-match erased (double-inj q1 N2 N1h d1 d2) (Refl _ _))
  (let-match erased sl01 (SLC _ _ _ _ s01))
  (let-match erased (rv-fn N2 A1 A rva1 rva (sl-tr A1 _ A (sl-sym _ A1 s01) sla)) (Refl _ _))
  (let-match erased vp1 (VPC x1 _ c1t _ _ px1 pr1 vp1t))
  (let-match erased nz1 (NZ1 _ _ _ _ nz1t))
  (let-match erased va1 (VAC _ _ _ _ _ _ ad1 va1t))
  (let ((erased bn) (erased pbn)) (pb-ex N2))
  (let ((erased bs) (erased pbs) (erased ngs)) (pb-s N2 bn pbn))
  (let ((erased bx) (erased pbx) (erased ngx)) (pb-s x1 bs (par-sub x1 (Succ N2) t00 bs ad1 pbs pt)))
  (let-match erased (ng-ng bx bs bn (ng-flip _ _ ngx) (ng-flip _ _ ngs)) (Refl _ _))
  (let ((erased c2) (erased w2) (erased B3) (erased p3) (erased pf3) (erased pm3) (erased vp2) (erased nz2) (erased ea3) (erased va3) (erased va4) (erased g2) (erased rc2))
    (up-run N2 (Succ x1) t00 (Succ x1) (Zero) c1t A (Cons (Nat) N4 R4) B2 (add-shift x1 N2 t00 ad1) (add-zero-right (Succ x1)) rva (RVE N4 t00 R4 d4 rv4)
      (sl-tr A _ (Cons (Nat) N4 R4) sla (SLC N4 r01 R4 rr (sl-sym rr R4 slr))) bn pbx pbn vp1t nz1t (halve x1 c1t B2 ea2)))
  (let-match erased vp2 (VPC x2 _ c2t _ b4 px2 pn4 vp2t))
  (let ((erased nz2t)) (nz-tl _ _ _ _ nz2))
  (let-match erased va3 (VAC _ a0 w20 _ At w2t ad3 va3t))
  (let-match erased va4 (VAC c1t0 _ _ c1tt _ _ ad4 va4t))
  (let-match erased va1t (VAC _ _ t0 _ _ T0tt ad5 va5t))
  (let-match erased aa (VAC _ _ _ _ _ _ ad7 aat))
  (let-match erased vo (VAC o0 a20 q0 Ot A2t Qt ad6 vot))
  (let-match erased vq (VAC _ _ _ _ _ _ ad8 vqt))
  (let-match erased (add-fn t0 (Zero) q0 t0 ad8 (add-zero-right t0)) (Refl _ _))
  (let ((erased e0)) (alg0 o0 a0 a20 t0 c1t0 x2 w20 N4 ad6 ad7 ad5 ad3 ad4))
  (let ((erased vtail)) (valg1 Ot At A2t Qt T0tt R4 R42 c1tt c2t w2t vot vqt aat rr2 va5t va3t va4t))
  (let ((erased b5) (erased px5) (erased ng5)) (pb-s x2 b4 px2))
  (let ((erased c3) (erased Rz) (erased w3) (erased rvz) (erased slz) (erased B4) (erased p4) (erased q4) (erased pf4) (erased pm4) (erased ng4) (erased vp3) (erased nz3) (erased ea4) (erased va5) (erased va6) (erased g3) (erased rc3))
    (dn-run N4 N4 (Zero) (Succ x2) (Succ o0) c2t R4 B3 (add-zero-right N4) (add-succ-right N4 o0 x2 (add-comm _ _ _ e0)) rv4 b5 b4 px5 pn4 (ng-flip _ _ ng5) vp2t nz2t (halve x2 c2t B3 ea3)))
  (let-match erased (va-zero (Zero) Rz c3 w3 rvz (Refl _ _) va5) (Refl _ _))
  (let-match erased (va-fn c2t R4 c3 Ot va6 vtail) (Refl _ _))
  (let-match erased ea4 (EAS _ _ _ lw))
  (let ((erased g5) (erased rc5)) (rcat _ _ _ _ _ rc2 rc3))
  (let ((erased g6) (erased rc6)) (rcat _ _ _ _ _ rc1 rc5))
  (values B4 lw (reach-catT p17 _ _ _ _ rcz rc6)))

(def-adts
  ((U2 : ((List (Nat)) xs) ((Nat) i) ((List (Nat)) ys) -> Type)
    enum
    (many U20 : (erased (Nat) x) (erased (List (Nat)) xs) -> (U2 (Cons (Nat) x xs) (Zero) (Cons (Nat) (Succ (Succ x)) xs)))
    (many U2S : (erased (Nat) x i) (erased (List (Nat)) xs ys) (erased (U2 xs i ys) u) -> (U2 (Cons (Nat) x xs) (Succ i) (Cons (Nat) x ys)))))

(def-fns _ $ (erased u2-fn : (erased (List (Nat)) x y y2) (erased (Nat) i) (subterm erased (U2 x i y) u) (erased (U2 x i y2) v) -> (erased (Eq (List (Nat)) y y2) e))
  (match erased u _
    ((U20 _ _) (let-match erased v (U20 _ _)) (Refl _ y))
    ((U2S x0 i1 xs ys u1) (let-match erased v (U2S _ _ _ ys2 v1)) (let-match erased (u2-fn xs ys ys2 i1 u1 v1) (Refl _ _)) (Refl _ y))))

(def-fns _ $ (erased u2-sl : (erased (List (Nat)) x y z) (erased (Nat) i) (subterm erased (U2 x i y) u) (erased (SL x z) s) -> (erased (SL y z) s2))
  (match erased u _
    ((U20 x0 xs) (let-match erased s (SLC _ z0 _ zs s1)) (SLC (Succ (Succ x0)) z0 xs zs s1))
    ((U2S x0 i1 xs ys u1) (let-match erased s (SLC _ z0 _ zs s1)) (SLC x0 z0 ys zs (u2-sl xs ys zs i1 u1 s1)))))

(def-fns _ $ (erased pb-ss : (erased (Nat) n) (erased (Bool) b) (erased (PB n b) p) -> (erased (PB (Succ (Succ n)) b) q))
  (match erased b (((PB (Succ (Succ n)) b) q)) ((BFalse) (PBF (Succ n) (PBT n p))) ((BTrue) (PBT (Succ n) (PBF n p)))))

(def-fns _ $ (erased zc-u2 : (erased (List (Nat)) c c2) (erased (Nat) i) (subterm erased (U2 c i c2) u) (erased (ZC c) zc) -> (erased (ZC c2) zc2))
  (match erased u _
    ((U20 x0 xs)
      (match erased zc _
        ((ZCL _ p) (ZCL (Succ (Succ x0)) (pb-ss x0 _ p)))
        ((ZCC x1 _ p z1) (ZCC (Succ (Succ x1)) xs (pb-ss (Succ x1) _ p) z1))))
    ((U2S x0 i1 xs ys u1)
      (let-match erased zc (ZCC x1 _ p z1) (absurd (ZCL _ _) u1))
      (ZCC x1 ys p (zc-u2 xs ys i1 u1 z1)))))

(def-fns _ $ (erased ze-u2 : (erased (List (Nat)) c c2 z) (erased (Nat) i) (subterm erased (U2 c i c2) u) (erased (ZE c z) ze) -> (erased (List (Nat)) z2) (erased (ZE c2 z2) ze2) (erased (U2 z i z2) u2))
  (match erased u _
    ((U20 x0 xs)
      (match erased ze _
        ((ZEL _) (values (Cons (Nat) (Succ (Succ (Succ x0))) (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat))))) (ZEL (Succ (Succ x0))) (U20 (Succ x0) (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Nil (Nat)))))))
        ((ZEC _ _ ys z1) (values (Cons (Nat) (Succ (Succ x0)) ys) (ZEC (Succ (Succ x0)) xs ys z1) (U20 x0 ys)))))
    ((U2S x0 i1 xs ys u1)
      (let-match erased ze (ZEC _ _ zs z1) (absurd (ZEL _) u1))
      (let ((erased zs2) (erased z2) (erased u3)) (ze-u2 xs ys zs i1 u1 z1))
      (values (Cons (Nat) x0 zs2) (ZEC x0 ys zs2 z2) (U2S x0 i1 zs zs2 u3)))))

(def-fns _ $ (erased va-u2-l : (erased (List (Nat)) x x2 y z) (erased (Nat) i) (subterm erased (U2 x i x2) u) (erased (VA x y z) v)
    -> (erased (List (Nat)) z2) (erased (U2 z i z2) u2) (erased (VA x2 y z2) v2))
  (match erased u _
    ((U20 a xs)
      (let-match erased v (VAC _ b c _ ys zs ad v1))
      (values (Cons (Nat) (Succ (Succ c)) zs) (U20 c zs) (VAC (Succ (Succ a)) b (Succ (Succ c)) xs ys zs (AddSucc (Succ a) b (Succ c) (AddSucc a b c ad)) v1)))
    ((U2S a i1 xs xs2 u1)
      (let-match erased v (VAC _ b c _ ys zs ad v1))
      (let ((erased zs2) (erased u3) (erased v3)) (va-u2-l xs xs2 ys zs i1 u1 v1))
      (values (Cons (Nat) c zs2) (U2S c i1 zs zs2 u3) (VAC a b c xs2 ys zs2 ad v3)))))

(def-fns _ $ (erased va-u2-r : (erased (List (Nat)) x y y2 z) (erased (Nat) i) (erased (U2 y i y2) u) (erased (VA x y z) v)
    -> (erased (List (Nat)) z2) (erased (U2 z i z2) u2) (erased (VA x y2 z2) v2))
  (let ((erased z2) (erased u2) (erased v2)) (va-u2-l y y2 x z i u (va-comm x y z v)))
  (values z2 u2 (va-comm y2 x z2 v2)))

(def-fns _ $ (erased va-u2-sw : (erased (List (Nat)) x x2 y y2 z) (erased (Nat) i) (subterm erased (U2 x i x2) u) (erased (U2 y2 i y) u2) (erased (VA x y z) v) -> (erased (VA x2 y2 z) v2))
  (match erased u _
    ((U20 a xs)
      (let-match erased u2 (U20 b ys))
      (let-match erased v (VAC _ _ c _ _ zs ad v1))
      (VAC (Succ (Succ a)) b c xs ys zs (add-shift (Succ a) b c (add-shift a (Succ b) c ad)) v1))
    ((U2S a i1 xs xs2 u1)
      (let-match erased u2 (U2S b _ ys ys2 u3))
      (let-match erased v (VAC _ _ c _ _ zs ad v1))
      (VAC a b c xs2 ys zs ad (va-u2-sw xs xs2 ys2 ys zs i1 u1 u3 v1)))))

(def-fns _ $ (erased ui-dbl : (erased (List (Nat)) x x2 xx) (erased (Nat) i) (subterm erased (UI x i x2) u) (erased (VA x x xx) v)
    -> (erased (List (Nat)) xx2) (erased (VA x2 x2 xx2) v2) (erased (U2 xx i xx2) u2))
  (match erased u _
    ((UI0 a xs)
      (let-match erased v (VAC _ _ c _ _ zs ad v1))
      (values (Cons (Nat) (Succ (Succ c)) zs) (VAC (Succ a) (Succ a) (Succ (Succ c)) xs xs zs (AddSucc a (Succ a) (Succ c) (add-succ-right a a c ad)) v1) (U20 c zs)))
    ((UIS a i1 xs xs2 u1)
      (let-match erased v (VAC _ _ c _ _ zs ad v1))
      (let ((erased zs2) (erased v3) (erased u3)) (ui-dbl xs xs2 zs i1 u1 v1))
      (values (Cons (Nat) c zs2) (VAC a a c xs2 xs2 zs2 ad v3) (U2S c i1 zs zs2 u3)))))

(def-fns _ $ (erased fo-ui : (erased (List (Nat)) r r2) (subterm erased (FO r r2) f) -> (erased (Nat) i) (erased (UI r i r2) u))
  (let-match erased f (FOeven x xs ys p f1) ((FOodd y z zs p) (values (Succ (Zero)) (UIS y _ _ _ (UI0 z zs)))))
  (let ((erased i) (erased u)) (fo-ui xs ys f1))
  (values (Succ i) (UIS (Succ x) i xs ys u)))

(def-fns _ $ (erased gst-ui : (erased (Nat) n) (erased (List (Nat)) r r2) (erased (GSt n r r2) g) -> (erased (Nat) i) (erased (UI r i r2) u))
  (match erased g _
    ((GSE _ q rs p) (values (Zero) (UI0 q rs)))
    ((GSO _ _ _ p f) (fo-ui r r2 f))))


(def-fns _ $ (erased u2-ex : (erased (List (Nat)) x y z) (erased (Nat) i) (subterm erased (U2 x i y) u) (erased (SL z x) s) -> (erased (List (Nat)) w) (erased (U2 z i w) u2))
  (match erased u _
    ((U20 x0 xs) (let-match erased s (SLC z0 _ zs _ _)) (values (Cons (Nat) (Succ (Succ z0)) zs) (U20 z0 zs)))
    ((U2S x0 i1 xs ys u1)
      (let-match erased s (SLC z0 _ zs _ s1))
      (let ((erased ws) (erased u3)) (u2-ex xs ys zs i1 u1 s1))
      (values (Cons (Nat) z0 ws) (U2S z0 i1 zs ws u3)))))

(def-fns _ $ (erased step-hi : (erased (Nat) N0 j N2 N4) (erased (List (Nat)) X O) (erased (Cy N0 X O N2 N4) cy) (erased (U2 X (Succ (Succ j)) O) u)
    -> (erased (List (Nat)) O2) (erased (Cy N0 O O2 N2 N4) cy2) (erased (U2 O j O2) u2))
  (let-match erased cy (MkCy _ x0 r00 r01 t00 N1h _ _ c z0 rs rr T0t A R4 A2 R42 Q _ tn p2 slc px zc ze vt pt a1 d2 rva sla d4 rv4 slr aa rr2 vo vq))
  (let-match erased u (U2S _ _ _ c2 u1))
  (let ((erased z2) (erased ze2) (erased uz)) (ze-u2 c c2 z0 (Succ j) u1 ze))
  (let ((erased T2) (erased ut) (erased vt2)) (va-u2-l z0 z2 _ _ (Succ j) uz vt))
  (let-match erased ut (U2S _ _ _ T0t2 ut1))
  (let ((erased Q2) (erased uq) (erased vq2)) (va-u2-l T0t T0t2 _ Q j ut1 vq))
  (let ((erased O2) (erased uo)) (u2-ex Q Q2 O j uq (va-sl O A2 Q vo)))
  (let ((erased Q3) (erased uq3) (erased vo2)) (va-u2-l O O2 A2 Q j uo vo))
  (let-match erased (u2-fn Q Q3 Q2 j uq3 uq) (Refl _ _))
  (values O2
    (MkCy N0 x0 r00 r01 t00 N1h N2 N4 c2 z2 rs rr T0t2 A R4 A2 R42 Q2 O2 tn p2 (u2-sl c c2 rs (Succ j) u1 slc) px (zc-u2 c c2 (Succ j) u1 zc) ze2
      vt2 pt a1 d2 rva sla d4 rv4 slr aa rr2 vo2 vq2)
    uo))

(def-adts
  ((Ctz : ((Nat) n) ((Nat) i) -> Type)
    enum
    (many CtzO : (erased (Nat) n) (erased (PB n (BTrue)) p) -> (Ctz n (Zero)))
    (many CtzE : (erased (Nat) m n i) (erased (Double m n) d) (erased (Ctz m i) c) -> (Ctz n (Succ i)))))

(def-fns _ $ (erased gst-uc : (erased (Nat) n) (erased (List (Nat)) r r2) (subterm erased (RV n r) rv) (erased (GSt n r r2) g)
    -> (erased (Nat) i) (erased (UI r i r2) u) (erased (Ctz (Succ n) i) c))
  (match erased rv _
    (absurd (RVN) (match erased g _ (absurd (GSO _ _ _ p _) p)))
    ((RVE q _ rs d rr)
      (let ((erased pe)) (double-pb q n d))
      (let-match erased g (GSE _ _ _ _) (absurd (GSO _ _ _ p _) (pb-fn n _ _ p pe)))
      (values (Zero) (UI0 q rs) (CtzO (Succ n) (PBT n pe))))
    ((RVO q n1 rs d rr)
      (let ((erased pe)) (double-pb q n1 d))
      (let-match erased g (GSO _ _ _ p fo) (absurd (GSE _ _ _ p) (pb-fn n _ _ p (PBT n1 pe))))
      (let-match erased fo (FOeven x _ ys px fo1)
        ((FOodd _ z zs py) (values (Succ (Zero)) (UIS (Succ q) _ _ _ (UI0 z zs)) (CtzE (Succ q) (Succ n) (Zero) (DS q n1 d) (CtzO (Succ q) py)))))
      (let ((erased pq) (erased pq1) (erased ng)) (pb-p q _ px))
      (let-match erased ng (NgT))
      (let ((erased i) (erased u) (erased c)) (gst-uc q rs ys rr (GSO q rs ys pq1 fo1)))
      (values (Succ i) (UIS (Succ q) i rs ys u) (CtzE (Succ q) (Succ n) i (DS q n1 d) c)))))

(def-adts
  ((SoT : ((Nat) n) ((List (Nat)) r) -> Type)
    enum
    (many SoS : (erased (Nat) n) (erased (List (Nat)) r r2) (erased (RV (Succ n) r2) rv) (erased (SL r r2) s) -> (SoT n r))
    (many SoTop : (erased (Nat) n) (erased (List (Nat)) r) (erased (TopN n r) t) -> (SoT n r))))

(def-fns _ $ (erased rv-sot : (erased (Nat) n) (erased (List (Nat)) r) (subterm erased (RV n r) rv) -> (erased (SoT n r) st))
  (let-match erased rv (RVO q n1 rs d rr)
    ((RVN) (SoTop (Zero) _ (TN0)))
    ((RVE q _ rs d rr) (SoS n _ _ (RVO q n rs d rr) (SLC q (Succ q) rs rs (sl-refl rs)))))
  (match erased (rv-sot q rs rr) _
    ((SoS _ _ rs2 rv2 s2) (SoS n _ _ (RVE (Succ q) (Succ n) rs2 (DS q n1 d) rv2) (SLC (Succ q) (Succ q) rs rs2 s2)))
    ((SoTop _ _ t) (SoTop n _ (TNS q n1 rs t d)))))

(def-fns _ $ (erased va-sl2 : (erased (List (Nat)) xs ys zs) (subterm erased (VA xs ys zs) v) -> (erased (SL xs ys) s))
  (let-match erased v (VAC x y z xs1 ys1 zs1 a v1) ((VAN) (SLN)))
  (SLC x y xs1 ys1 (va-sl2 xs1 ys1 zs1 v1)))

(def-fns _ $ (erased step-0 : (erased (Nat) N0 M N4) (erased (List (Nat)) X O) (erased (Cy N0 X O (Succ M) N4) cy) (erased (U2 X (Zero) O) u)
    -> (erased (List (Nat)) O2) (erased (Nat) i) (erased (Cy N0 O O2 M N4) cy2) (erased (U2 O i O2) u2) (erased (Ctz (Succ M) i) ct))
  (let-match erased cy (MkCy _ x0 r00 r01 t00 N1h _ _ c z0 rs rr T0t A R4 A2 R42 Q _ tn p2 slc px zc ze vt pt a1 d2 rva sla d4 rv4 slr aa rr2 vo vq))
  (let-match erased u (U20 _ _))
  (let-match erased d2 (DS _ N1g d3))
  (let ((erased A1) (erased rva1) (erased gs)) (rv-down M A rva))
  (let ((erased i) (erased ui) (erased ct)) (gst-uc M A1 A rva1 gs))
  (let ((erased sl1)) (sl-tr A1 A _ (gst-sl M A1 A gs) (sl-sym A _ sla)))
  (let ((erased A3) (erased aa3)) (va-ex A1 A1 (sl-refl A1)))
  (let ((erased A4) (erased aa4) (erased ua)) (ui-dbl A1 A A3 i ui aa3))
  (let-match erased (va-fn A A A4 A2 aa4 aa) (Refl _ _))
  (let ((erased O2) (erased uo)) (u2-ex A3 A2 O i ua (sl-tr O A2 A3 (va-sl2 O A2 Q vo) (sl-sym A2 A3 (u2-sl A3 A2 A3 i ua (sl-refl A3))))))
  (values O2 i
    (MkCy N0 (Succ (Succ x0)) r00 r01 t00 N1g M N4 c z0 rs rr T0t A1 R4 A3 R42 Q O2 tn p2 slc (pb-ss x0 _ px) zc ze vt pt
      (add-shift (Succ x0) (Succ N1g) N0 (add-shift x0 (Succ (Succ N1g)) N0 a1)) d3 rva1 sl1 d4 rv4 slr aa3 rr2 (va-u2-sw O O2 A2 A3 Q i uo ua vo) vq)
    uo ct))

(def-adts
  ((S1R : ((Nat) N0) ((List (Nat)) O) ((Nat) N2) ((Nat) N4) -> Type)
    enum
    (many S1Go : (erased (Nat) N0 N2 N4 i) (erased (List (Nat)) O O2) (erased (Cy N0 O O2 N2 (Succ N4)) cy) (erased (U2 O (Succ i) O2) u)
       (erased (Ctz (Succ N4) i) ct) -> (S1R N0 O N2 N4))
    (many S1Top : (erased (Nat) N0 N2 N4) (erased (List (Nat)) O) (erased (Eq (Nat) N4 N0) e) -> (S1R N0 O N2 N4))))

(def-fns _ $ (erased p2-len : (erased (List (Nat)) xs ys) (subterm erased (P2 xs ys) p) -> (erased (SL ys (Cons (Nat) (Zero) (Cons (Nat) (Zero) xs))) s))
  (let-match erased p (P2C x xs1 ys1 p1) ((P2N) (sl-refl _)))
  (let ((erased s1)) (p2-len xs1 ys1 p1))
  (sl-tr (Cons (Nat) x ys1) (Cons (Nat) (Zero) (Cons (Nat) (Zero) (Cons (Nat) (Zero) xs1))) _ (SLC x (Zero) ys1 _ s1)
    (SLC (Zero) (Zero) _ _ (SLC (Zero) (Zero) _ _ (SLC x (Zero) xs1 xs1 (sl-refl xs1))))))

(def-fns _ $ (erased p2-sl : (erased (List (Nat)) rs) (erased (Nat) a b) (erased (List (Nat)) rr) (erased (P2 rs (Cons (Nat) a (Cons (Nat) b rr))) p) -> (erased (SL rr rs) s))
  (let-match erased (p2-len rs _ p) (SLC _ _ _ _ s1))
  (let-match erased s1 (SLC _ _ _ _ s2))
  s2)

(def-fns _ $ (erased step-1 : (erased (Nat) N0 N2 N4) (erased (List (Nat)) X O) (erased (Cy N0 X O N2 N4) cy) (erased (U2 X (Succ (Zero)) O) u)
    -> (erased (S1R N0 O N2 N4) r))
  (let-match erased cy (MkCy _ x0 r00 r01 t00 N1h _ _ c z0 rs rr T0t A R4 A2 R42 Q _ tn p2 slc px zc ze vt pt a1 d2 rva sla d4 rv4 slr aa rr2 vo vq))
  (let-match erased (rv-sot N4 R4 rv4) (SoS _ _ R5 rv5 sl45)
    ((SoTop _ _ t4) (S1Top N0 N2 N4 O (topn-fn N4 N0 R4 rs t4 tn (sl-tr R4 rr rs (sl-sym rr R4 slr) (sl-sym rr rs (p2-sl rs r00 r01 rr p2)))))))
  (let-match erased u (U2S _ _ _ c2 u1))
  (let ((erased z2) (erased ze2) (erased uz)) (ze-u2 c c2 z0 (Zero) u1 ze))
  (let ((erased T2) (erased ut) (erased vt2)) (va-u2-l z0 z2 _ _ (Zero) uz vt))
  (let-match erased ut (U20 _ _))
  (let ((erased R4c) (erased rv4c) (erased gs)) (rv-down N4 R5 rv5))
  (let-match erased (rv-fn N4 R4c R4 rv4c rv4 (sl-tr R4c R5 R4 (gst-sl N4 R4c R5 gs) sl45)) (Refl _ _))
  (let ((erased i) (erased ui) (erased ct)) (gst-uc N4 R4 R5 rv4 gs))
  (let ((erased R43) (erased rr3) (erased u42)) (ui-dbl R4 R5 R42 i ui rr2))
  (let ((erased Q2) (erased uq) (erased vq2)) (va-u2-r T0t _ _ Q (Succ i) (U2S (Zero) i R42 R43 u42) vq))
  (let ((erased O2) (erased uo)) (u2-ex Q Q2 O (Succ i) uq (va-sl O A2 Q vo)))
  (let ((erased Q3) (erased uq3) (erased vo2)) (va-u2-l O O2 A2 Q (Succ i) uo vo))
  (let-match erased (u2-fn Q Q3 Q2 (Succ i) uq3 uq) (Refl _ _))
  (S1Go N0 N2 N4 i O O2
    (MkCy N0 x0 r00 r01 (Succ (Succ t00)) N1h N2 (Succ N4) c2 z2 rs rr T0t A R5 A2 R43 Q2 O2 tn p2 (u2-sl c c2 rs (Zero) u1 slc) px (zc-u2 c c2 (Zero) u1 zc) ze2
      vt2 (pb-ss t00 _ pt) a1 d2 rva sla (DS N4 t00 d4) rv5 (sl-tr rr R4 R5 slr (sl-sym R4 R5 sl45)) aa rr3 vo2 vq2)
    uo ct))


(def-fns _ $ (erased ctz-pos : (erased (Nat) n i) (subterm erased (Ctz n i) c) -> (erased (Nat) n1) (erased (Eq (Nat) n (Succ n1)) e))
  (match erased c _
    ((CtzO _ p) (let-match erased p (PBT n1 _)) (values n1 (Refl _ n)))
    ((CtzE m _ i1 d c1)
      (let ((erased m1) (erased e1)) (ctz-pos m i1 c1))
      (let-match erased e1 (Refl _ _))
      (let-match erased d (DS _ b _))
      (values (Succ b) (Refl _ n)))))

(def-fns _ $ (erased ctz-fn : (erased (Nat) n i j) (subterm erased (Ctz n i) c) (erased (Ctz n j) d) -> (erased (Eq (Nat) i j) e))
  (match erased c _
    ((CtzO _ p)
      (let-match erased d (CtzO _ _) (absurd (CtzE m _ j1 dd c1) (pb-fn n _ _ p (double-pb m n dd))))
      (Refl _ i))
    ((CtzE m _ i1 dd c1)
      (let-match erased d (CtzE m2 _ j1 dd2 d1) (absurd (CtzO _ p) (pb-fn n _ _ p (double-pb m n dd))))
      (let-match erased (double-inj m m2 n dd dd2) (Refl _ _))
      (let-match erased (ctz-fn m i1 j1 c1 d1) (Refl _ _))
      (Refl _ i))))

(def-fns _ $ (erased add-double : (erased (Nat) a b c a2 b2) (subterm erased (Add a b c) s) (erased (Double a a2) da) (erased (Double b b2) db) -> (erased (Nat) c2) (erased (Add a2 b2 c2) s2) (erased (Double c c2) dc))
  (let-match erased s (AddSucc a1 _ c1 s1) ((AddZero _) (let-match erased da (D0)) (values b2 (AddZero b2) db)))
  (let-match erased da (DS _ a3 da1))
  (let ((erased c3) (erased s3) (erased dc3)) (add-double a1 b c1 a3 b2 s1 da1 db))
  (values (Succ (Succ c3)) (AddSucc (Succ a3) b2 (Succ c3) (AddSucc a3 b2 c3 s3)) (DS c1 c3 dc3)))

(def-fns _ $ (erased add-halve : (erased (Nat) a2 b2 c2 a b) (subterm erased (Add a2 b2 c2) s) (erased (Double a a2) da) (erased (Double b b2) db) -> (erased (Nat) c) (erased (Add a b c) s2) (erased (Double c c2) dc))
  (let-match erased da (DS a1 a3 da1) ((D0) (let-match erased s (AddZero _)) (values b (AddZero b) db)))
  (let-match erased s (AddSucc _ _ c3 s1))
  (let-match erased s1 (AddSucc _ _ c4 s3))
  (let ((erased c) (erased s4) (erased dc)) (add-halve a3 b2 c4 a1 b s3 da1 db))
  (values (Succ c) (AddSucc a1 b c s4) (DS c c4 dc)))

(def-fns _ $ (erased ctz-sum : (erased (Nat) a b i j N) (erased (List (Nat)) rs) (subterm erased (TopN N rs) t) (erased (Ctz a i) ca) (erased (Ctz b j) cb) (erased (Add a b (Succ N)) s) -> (erased (Eq (Nat) i j) e))
  (let ((erased a1) (erased ea)) (ctz-pos a i ca))
  (let-match erased ea (Refl _ _))
  (let ((erased b1) (erased eb)) (ctz-pos b j cb))
  (let-match erased eb (Refl _ _))
  (let-match erased t (TNS q n rs1 t1 d)
    (absurd (TN0) (let-match erased s (AddSucc _ _ _ s1)) s1))
  (let ((erased pN)) (PBF (Succ n) (PBT n (double-pb q n d))))
  (match erased ca _
    ((CtzO _ pa)
      (let-match erased cb (CtzO _ _)
        (absurd (CtzE m _ j1 db cb1)
          (let ((erased pc) (erased qc) (erased x)) (par-add a b (Succ (Succ n)) (BTrue) (BFalse) s pa (double-pb m b db)))
          (let-match erased (pb-fn _ _ _ qc pN) (Refl _ _))
          x))
      (Refl _ i))
    ((CtzE ma _ i1 da ca1)
      (let-match erased cb (CtzE mb _ j1 db cb1)
        (absurd (CtzO _ pb)
          (let ((erased pc) (erased qc) (erased x)) (par-add a b (Succ (Succ n)) (BFalse) (BTrue) s (double-pb ma a da) pb))
          (let-match erased (pb-fn _ _ _ qc pN) (Refl _ _))
          x))
      (let ((erased c) (erased s2) (erased dc)) (add-halve a b (Succ (Succ n)) ma mb s da db))
      (let-match erased (double-inj c (Succ q) (Succ (Succ n)) dc (DS q n d)) (Refl _ _))
      (let-match erased (ctz-sum ma mb i1 j1 q rs1 t1 ca1 cb1 s2) (Refl _ _))
      (Refl _ i))))

(def-adts
  ((NO : ((Nat) a) ((Nat) b) -> Type)
    enum
    (many NOZ : (erased (Nat) a) -> (NO a a))
    (many NOS : (erased (Nat) a b i) (erased (NO a b) n) (erased (Ctz (Succ b) i) c) (erased (PB i (BFalse)) p) -> (NO a (Succ b)))))

(def-fns _ $ (erased no-le : (erased (Nat) a b) (subterm erased (NO a b) n) -> (erased (Lt a (Succ b)) l))
  (match erased n _
    ((NOZ _) (lt-succ a))
    ((NOS _ b1 i n1 c p) (lt-weaken a (Succ b1) (no-le a b1 n1)))))

(def-fns _ $ (erased no-drop : (erased (Nat) a b) (subterm erased (NO a b) n) (erased (Lt a b) l) -> (erased (NO (Succ a) b) r))
  (let-match erased n (NOS _ b1 i n1 c p) (absurd (NOZ _) (lt-asym a a l (lt-weaken a a l))))
  (let-match erased (lt-succ-cases a b1 l) (InR _ _ l1) ((InL _ _ e) (let-match erased e (Refl _ _)) (NOZ (Succ a))))
  (NOS (Succ a) b1 i (no-drop a b1 n1 l1) c p))

(def-fns _ $ (erased no-look : (erased (Nat) a b v i) (subterm erased (NO a b) n) (erased (Lt a v) l1) (erased (Lt v (Succ b)) l2) (erased (Ctz v i) c) -> (erased (PB i (BFalse)) p))
  (let-match erased n (NOS _ b1 i1 n1 c1 p1) (absurd (NOZ _) (lt-asym a v l1 l2)))
  (let-match erased (lt-succ-cases v (Succ b1) l2) (InR _ _ l3)
    ((InL _ _ e) (let-match erased e (Refl _ _)) (let-match erased (ctz-fn v i i1 c c1) (Refl _ _)) p1))
  (no-look a b1 v i n1 l1 l3 c))

(def-fns _ $ (erased double-le : (erased (Nat) a b a2 b2) (subterm erased (Lt a (Succ b)) l) (erased (Double a a2) da) (erased (Double b b2) db) -> (erased (Lt a2 (Succ b2)) r))
  (let-match erased da (DS a1 a3 da1) ((D0) (LtZ b2)))
  (let-match erased db (DS b1 b3 db1) (absurd (D0) (let-match erased l (LtS _ _ l1)) l1))
  (let-match erased l (LtS _ _ l1))
  (LtS (Succ a3) (Succ (Succ b3)) (LtS a3 (Succ b3) (double-le a1 b1 a3 b3 l1 da1 db1))))

(def-fns _ $ (erased rv-le-top : (erased (Nat) n N) (erased (List (Nat)) r t) (subterm erased (RV n r) rv) (erased (TopN N t) tn) (erased (SL r t) s) -> (erased (Lt n (Succ N)) l))
  (match erased rv _
    ((RVN) (let-match erased s (SLN)) (let-match erased tn (TN0)) (LtZ (Zero)))
    ((RVE q _ rs d rr)
      (let-match erased s (SLC _ _ _ t1 s1))
      (let-match erased tn (TNS q2 N1 _ tn1 d2))
      (lt-weaken n (Succ N1) (double-le q q2 n N1 (rv-le-top q q2 rs t1 rr tn1 s1) d d2)))
    ((RVO q n1 rs d rr)
      (let-match erased s (SLC _ _ _ t1 s1))
      (let-match erased tn (TNS q2 N1 _ tn1 d2))
      (LtS n1 (Succ N1) (double-le q q2 n1 N1 (rv-le-top q q2 rs t1 rr tn1 s1) d d2)))))

(def-fns _ $ (erased pb-half : (erased (Nat) n) (subterm erased (PB n (BFalse)) p) -> (erased (Nat) m) (erased (Double m n) d))
  (let-match erased p (PBF n1 p1) ((PB0) (values (Zero) (D0))))
  (let-match erased p1 (PBT n2 p2))
  (let ((erased m) (erased d)) (pb-half n2 p2))
  (values (Succ m) (DS m n2 d)))

(def-fns _ $ (erased ctz-ex : (subterm erased (Nat) n) -> (erased (Nat) i) (erased (Ctz (Succ n) i) c))
  (let ((erased b) (erased p)) (pb-ex (Succ n)))
  (let-match erased b (BFalse) ((BTrue) (values (Zero) (CtzO (Succ n) p))))
  (let ((erased m) (erased d)) (pb-half (Succ n) p))
  (let-match erased d (DS m1 b1 d1))
  (let ((erased i) (erased c)) (ctz-ex (subterm (lt-subterm m1 n (double-lt m1 b1 d1))) m1))
  (values (Succ i) (CtzE (Succ m1) (Succ n) i (DS m1 b1 d1) c)))

(def-adts
  ((MB : ((Nat) M) ((Nat) h) -> Type)
    enum
    (many MBB : (erased (Nat) h) -> (MB (Succ h) h))
    (many MBO : (erased (Nat) M h k) (erased (Ctz M k) c) (erased (PB k (BTrue)) p) -> (MB M h))))

(def-adts
  ((BC : ((Nat) J) ((Nat) M) ((Nat) N4) ((Nat) h) -> Type)
    enum
    (many BCO : (erased (Nat) J M N4 h) (erased (PB J (BTrue)) pj) (erased (NO M N4) n) (erased (MB M h) mb) -> (BC J M N4 h))
    (many BCE : (erased (Nat) J M w h k) (erased (PB J (BFalse)) pj) (erased (NO M w) n) (erased (Ctz (Succ w) k) c) (erased (PB k (BTrue)) pk) -> (BC J M (Succ w) h))))

(def-adts
  ((Ph : ((Nat) N0) ((List (Nat)) X) ((Nat) J) -> Type)
    enum
    (many MkPh : (erased (Nat) N0 J N2 N4 M N0d N0h) (erased (List (Nat)) X O rs)
       (erased (Cy N0 X O N2 N4) cy) (erased (U2 X J O) u) (erased (Add M N2 N0) am)
       (erased (TopN N0 rs) tn) (erased (Eq (Nat) N0 (Succ N0d)) e0) (erased (Double N0h N0d) d0) (erased (PB N0h (BTrue)) po)
       (erased (BC J M N4 N0h) bc) -> (Ph N0 X J))))

(def-fns _ $ (erased cy-n4 : (erased (Nat) N0 N2 N4) (erased (List (Nat)) X O) (erased (Cy N0 X O N2 N4) cy) -> (erased (Lt N4 (Succ N0)) l))
  (let-match erased cy (MkCy _ x0 r00 r01 t00 N1h _ _ c z0 rs rr T0t A R4 A2 R42 Q _ tn p2 slc px zc ze vt pt a1 d2 rva sla d4 rv4 slr aa rr2 vo vq))
  (rv-le-top N4 N0 R4 rs rv4 tn (sl-tr R4 rr rs (sl-sym rr R4 slr) (sl-sym rr rs (p2-sl rs r00 r01 rr p2)))))

(def-fns _ $ (erased cy-ex : (erased (Nat) N0 N2 N4) (erased (List (Nat)) X O) (erased (Cy N0 X O N2 N4) cy)
    -> (erased (Nat) x0) (erased (List (Nat)) c) (erased (Eq (List (Nat)) X (Cons (Nat) x0 c)) e))
  (let-match erased cy (MkCy _ x0 r00 r01 t00 N1h _ _ c z0 rs rr T0t A R4 A2 R42 Q _ tn p2 slc px zc ze vt pt a1 d2 rva sla d4 rv4 slr aa rr2 vo vq))
  (values x0 c (Refl _ X)))

(def-adts
  ((PR : ((Nat) N0) ((List (Bool)) B) -> Type)
    enum
    (many PNext : (erased (Nat) N0 J2) (erased (List (Nat)) X2) (erased (List (Bool)) B B2) (erased (Ph N0 X2 J2) ph) (erased (Lw X2 B2) lw)
       (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) (BTrue)) rc) -> (PR N0 B))
    (many PTop : (erased (Nat) N0) (erased (List (Nat)) X O) (erased (List (Bool)) B B2) (erased (Cy N0 X O (Succ (Zero)) N0) cy) (erased (U2 X (Succ (Zero)) O) u)
       (erased (Lw O B2) lw) (erased (Reach p17 (MkTc 2 (DL) B (bits "0")) (MkTc 2 (DL) B2 (bits "0")) (BTrue)) rc) -> (PR N0 B))))

(def-fns _ $ (erased pb-ss-inv : (erased (Nat) n) (erased (Bool) b) (erased (PB (Succ (Succ n)) b) p) -> (erased (PB n b) q))
  (match erased p _ ((PBF _ p1) (let-match erased p1 (PBT _ p2)) p2) ((PBT _ p1) (let-match erased p1 (PBF _ p2)) p2)))

(def-fns _ $ (erased double-self : (erased (Nat) h) (erased (Double h h) d) -> (erased (Eq (Nat) h (Zero)) e))
  (let-match erased d (D0) (absurd (DS h1 b d1) (let ((erased l)) (double-lt h1 b d1)) (lt-asym h1 h1 l (lt-weaken h1 h1 l))))
  (Refl _ h))

(def-fns _ $ (erased ph-step : (erased (Nat) N0 J) (erased (List (Nat)) X) (erased (List (Bool)) B) (erased (Ph N0 X J) ph) (erased (Lw X B) lw) -> (erased (PR N0 B) r))
  (let-match erased ph (MkPh _ _ N2 N4 M N0d N0h _ O rs cy u am tn e0 d0 po bc))
  (let ((erased x0) (erased c) (erased ex)) (cy-ex N0 N2 N4 X O cy))
  (let-match erased ex (Refl _ _))
  (let ((erased B2) (erased lw2) (erased rc)) (cycle N0 x0 N2 N4 c O B cy (EAS x0 c B lw)))
  (let-match erased J (Succ J1)
    ((Zero)
      (let-match erased bc (BCE _ _ w _ k _ n ck pk) (absurd (BCO _ _ _ _ pj _ _) pj))
      (let ((erased lmn)) (lt-le-trans M (Succ w) N0 (no-le M w n) (cy-n4 N0 N2 N4 X O cy)))
      (let-match erased N2 (Succ M2)
        (absurd (Zero) (let-match erased (add-fn M (Zero) N0 M am (add-zero-right M)) (Refl _ _)) (lt-asym M M lmn (lt-weaken M M lmn))))
      (let ((erased O2) (erased i) (erased cy2) (erased u2) (erased ct)) (step-0 N0 M2 N4 X O cy u))
      (let ((erased i2) (erased ct2)) (ctz-ex M))
      (let-match erased (ctz-sum (Succ M) (Succ M2) i2 i N0 rs tn ct2 ct (AddSucc M (Succ M2) N0 am)) (Refl _ _))
      (let ((erased bi) (erased pi)) (pb-ex i))
      (let ((erased am2)) (add-shift M M2 N0 am))
      (match erased bi (((PR N0 B) r))
        ((BTrue)
          (let-match erased (lt-succ-cases M w (no-le M w n)) (InL _ _ e)
            (absurd (InR _ _ l) (pb-fn i _ _ pi (no-look M w (Succ M) i n (lt-succ M) (LtS M w l) ct2))))
          (let-match erased e (Refl _ _))
          (PNext N0 i O B B2 (MkPh N0 i M2 N4 (Succ M) N0d N0h O O2 rs cy2 u2 am2 tn e0 d0 po (BCO i (Succ M) N4 N0h pi (NOZ N4) (MBO (Succ M) N0h i ct2 pi))) lw2 rc))
        ((BFalse)
          (let-match erased (lt-succ-cases M w (no-le M w n)) (InR _ _ l)
            (absurd (InL _ _ e) (let-match erased e (Refl _ _)) (let-match erased (ctz-fn (Succ M) i k ct2 ck) (Refl _ _)) (pb-fn i _ _ pi pk)))
          (PNext N0 i O B B2 (MkPh N0 i M2 N4 (Succ M) N0d N0h O O2 rs cy2 u2 am2 tn e0 d0 po (BCE i (Succ M) w N0h k pi (no-drop M w n l) ck pk)) lw2 rc)))))
  (let-match erased J1 (Succ j)
    ((Zero)
      (let-match erased bc (BCO _ _ _ _ pj n mb) (absurd (BCE _ _ _ _ _ pj _ _ _) (let-match erased pj (PBF _ q)) q))
      (match erased (step-1 N0 N2 N4 X O cy u) (((PR N0 B) r))
        ((S1Go _ _ _ i _ O2 cy2 u2 ct)
          (let ((erased bi) (erased pi)) (pb-ex i))
          (match erased bi (((PR N0 B) r))
            ((BFalse) (PNext N0 (Succ i) O B B2 (MkPh N0 (Succ i) N2 (Succ N4) M N0d N0h O O2 rs cy2 u2 am tn e0 d0 po (BCO (Succ i) M (Succ N4) N0h (PBT i pi) (NOS M N4 i n ct pi) mb)) lw2 rc))
            ((BTrue) (PNext N0 (Succ i) O B B2 (MkPh N0 (Succ i) N2 (Succ N4) M N0d N0h O O2 rs cy2 u2 am tn e0 d0 po (BCE (Succ i) M N4 N0h i (PBF i pi) n ct pi)) lw2 rc))))
        ((S1Top _ _ _ _ e4)
          (let-match erased e4 (Refl _ _))
          (let-match erased e0 (Refl _ _))
          (let ((erased pd)) (double-pb N0h N0d d0))
          (let-match erased (lt-succ-cases M N0 (no-le M N0 n)) (InR _ _ l1)
            (absurd (InL _ _ e)
              (let-match erased e (Refl _ _))
              (match erased mb _
                (absurd (MBB _) (let-match erased (double-self N0h d0) (Refl _ _)) po)
                (absurd (MBO _ _ k ck pk)
                  (let-match erased (ctz-fn N0 k (Zero) ck (CtzO N0 (PBT N0d pd))) (Refl _ _))
                  pk))))
          (let-match erased (lt-succ-cases M N0d l1) (InL _ _ e)
            (absurd (InR _ _ l2) (pb-fn _ _ _ (PBT (Zero) (PB0)) (no-look M N0 N0d (Succ (Zero)) n l2 (lt-weaken N0d (Succ N0d) (lt-succ N0d)) (CtzE N0h N0d (Zero) d0 (CtzO N0h po))))))
          (let-match erased e (Refl _ _))
          (let-match erased (add-cancel N0d N2 (Succ (Zero)) (Succ N0d) am (add-comm _ _ _ (AddSucc (Zero) N0d N0d (AddZero N0d)))) (Refl _ _))
          (PTop N0 X O B B2 cy u lw2 rc)))))
  (let ((erased O2) (erased cy2) (erased u2)) (step-hi N0 j N2 N4 X O cy u))
  (let ((erased bc2)) (match erased bc (((BC j M N4 N0h) b))
    ((BCO _ _ _ _ pj n mb) (BCO j M N4 N0h (pb-ss-inv j _ pj) n mb))
    ((BCE _ _ w _ k pj n ck pk) (BCE j M w N0h k (pb-ss-inv j _ pj) n ck pk))))
  (PNext N0 j O B B2 (MkPh N0 j N2 N4 M N0d N0h O O2 rs cy2 u2 am tn e0 d0 po bc2) lw2 rc))
