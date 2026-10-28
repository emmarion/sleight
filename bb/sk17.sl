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
