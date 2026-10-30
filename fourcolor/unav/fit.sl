; Certified part semantics after part.v, over the types of part.sl. A part is read against Obs, the arities seen around
; a hub dart: per sector the spoke arity a, the hat arity h and the fan arities, so that everything here is about lists
; and numbers; map.sl ties Obs to a hypermap. A range MkRg lo hi holds an arity whose value clamped at 9 lies in [lo, hi].

(unary 9 8)

(def-adts $ (Both : (Type P) (Type Q) -> Type)
  enum
  (many MkBoth : (erased Type P Q) (erased P p) (erased Q q) -> (Both P Q)))

(def-adts $ (Clamp : ((Nat) a m) -> Type)
  enum
  (many ClLo : (erased (Nat) a) (erased (Lt a 9) p) -> (Clamp a a))
  (many ClHi : (erased (Nat) a) (erased (Lt 8 a) p) -> (Clamp a 9)))

(def-adts $ (InRg : ((Nat) a) ((Rg) r) -> Type)
  enum
  (many MkInRg : (erased (Nat) a m lo hi) (erased (Clamp a m) c) (erased (Lt lo (Succ m)) l) (erased (Lt m (Succ hi)) u)
      -> (InRg a (MkRg lo hi))))

(def-adts $ (OutRg : ((Nat) a) ((Rg) r) -> Type)
  enum
  (many OutLo : (erased (Nat) a m lo hi) (erased (Clamp a m) c) (erased (Lt m lo) l) -> (OutRg a (MkRg lo hi)))
  (many OutHi : (erased (Nat) a m lo hi) (erased (Clamp a m) c) (erased (Lt hi m) u) -> (OutRg a (MkRg lo hi))))

(def-adts $ (RgSub : ((Rg) r q) -> Type)
  enum
  (many MkRgSub : (erased (Nat) a b c d) (erased (Lt c (Succ a)) l) (erased (Lt b (Succ d)) u) -> (RgSub (MkRg a b) (MkRg c d))))

(def-adts $ (RgDis : ((Rg) r q) -> Type)
  enum
  (many DisLo : (erased (Nat) a b c d) (erased (Lt b c) l) -> (RgDis (MkRg a b) (MkRg c d)))
  (many DisHi : (erased (Nat) a b c d) (erased (Lt d a) u) -> (RgDis (MkRg a b) (MkRg c d))))

; z holds every arity that both r and q hold.
(def-adts $ (Weak : ((Rg) r q z) -> Type)
  enum
  (many WkL : (erased (Rg) r q) -> (Weak r q r))
  (many WkR : (erased (Rg) r q) -> (Weak r q q))
  (many WkM : (erased (Nat) a b c d e g) (erased (Or (Eq (Nat) e a) (Eq (Nat) e c)) se) (erased (Or (Eq (Nat) g b) (Eq (Nat) g d)) sg)
      -> (Weak (MkRg a b) (MkRg c d) (MkRg e g))))

(def-adts $ (Ans : ((Rel) c) (Type P) (Type N) -> Type)
  enum
  (many AnsSub : (erased Type P N) (erased P p) -> (Ans (PSub) P N))
  (many AnsDis : (erased Type P N) (erased N n) -> (Ans (PDis) P N))
  (many AnsStr : (erased Type P N) -> (Ans (PStr) P N)))

(def-adts $ (Ord2 : ((Nat) a b) -> Type)
  enum
  (many LeY : (erased (Nat) a b) (erased (Lt a (Succ b)) p) -> (Ord2 a b))
  (many LeN : (erased (Nat) a b) (erased (Lt b a) p) -> (Ord2 a b)))

(def-fns _ $ (many le-dec : (many (Nat) a b) -> (many (Ord2 a b) o))
  (match many (nat-cmp a b) _
    ((CLt _ _ _ _ p) (LeY a b (lt-weaken a b p)))
    ((CEq _ _ _) (LeY a a (lt-succ a)))
    ((CGt _ _ _ _ q) (LeN a b q))))

(def-fns _ $ (erased le-trans : (erased (Nat) a b c) (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a (Succ c)) r))
  (lt-le-trans a (Succ b) (Succ c) p (LtS b (Succ c) q)))

(def-fns _ $ (erased absurd lt-le-absurd : (erased (Nat) a b) (erased (Lt a b) p) (erased (Lt b (Succ a)) q) -> (erased (False) f))
  (lt-asym a b p q))

(def-fns _ $ (erased clamp-exists : (erased (Nat) a) -> (erased (Nat) m) (erased (Clamp a m) c))
  (match erased (nat-cmp a 9) _
    ((CLt _ _ _ _ p) (values a (ClLo a p)))
    ((CEq _ _ _) (values 9 (ClHi 9 (lt-succ 8))))
    ((CGt _ _ _ _ q) (values 9 (ClHi a (lt-trans 8 9 a (lt-succ 8) q))))))

(def-fns _ $ (erased clamp-fn : (erased (Nat) a m k) (erased (Clamp a m) c) (erased (Clamp a k) d) -> (erased (Eq (Nat) m k) e))
  (match erased c _
    ((ClLo _ p) (match erased d _ ((ClLo _ _) (Refl _ a)) (absurd (ClHi _ q) (lt-le-absurd 8 a q p))))
    ((ClHi _ p) (match erased d _ (absurd (ClLo _ q) (lt-le-absurd 8 a p q)) ((ClHi _ _) (Refl _ 9))))))

(def-fns _ $ (erased absurd in-out : (erased (Nat) a) (erased (Rg) r) (erased (InRg a r) p) (erased (OutRg a r) q) -> (erased (False) f))
  (let-match erased p (MkInRg _ m lo hi c l u))
  (match erased q _
    (absurd (OutLo _ k _ _ d l2) (let-match erased (clamp-fn a m k c d) (Refl _ _)) (lt-le-absurd m lo l2 l))
    (absurd (OutHi _ k _ _ d u2) (let-match erased (clamp-fn a m k c d) (Refl _ _)) (lt-le-absurd hi m u2 u))))

(def-fns _ $ (erased rg-sub : (erased (Nat) a) (erased (Rg) r q) (erased (InRg a r) p) (erased (RgSub r q) s) -> (erased (InRg a q) t))
  (let-match erased p (MkInRg _ m lo hi c l u))
  (let-match erased s (MkRgSub _ _ c2 d2 l2 u2))
  (MkInRg a m c2 d2 c (le-trans c2 lo m l2 l) (le-trans m hi d2 u u2)))

(def-fns _ $ (erased rg-dis : (erased (Nat) a) (erased (Rg) r q) (erased (InRg a r) p) (erased (RgDis r q) s) -> (erased (OutRg a q) t))
  (let-match erased p (MkInRg _ m lo hi c l u))
  (match erased s _
    ((DisLo _ _ c2 d2 l2) (OutLo a m c2 d2 c (lt-le-trans m (Succ hi) c2 u (LtS hi c2 l2))))
    ((DisHi _ _ c2 d2 u2) (OutHi a m c2 d2 c (lt-le-trans d2 lo m u2 l)))))

(def-fns _ $ (erased rg-weak : (erased (Nat) x) (erased (Rg) r q z) (erased (InRg x r) p) (erased (InRg x q) p2) (erased (Weak r q z) w)
    -> (erased (InRg x z) t))
  (let-match erased w (WkM a b c d e g se sg) ((WkL _ _) p) ((WkR _ _) p2))
  (let-match erased p (MkInRg _ m _ _ cl la ua))
  (let-match erased p2 (MkInRg _ k _ _ cl2 lc uc))
  (let-match erased (clamp-fn x m k cl cl2) (Refl _ _))
  (MkInRg x m e g cl
    (match erased se _ ((OrL _ _ ea) (let-match erased ea (Refl _ _)) la) ((OrR _ _ ec) (let-match erased ec (Refl _ _)) lc))
    (match erased sg _ ((OrL _ _ eb) (let-match erased eb (Refl _ _)) ua) ((OrR _ _ ed) (let-match erased ed (Refl _ _)) uc))))

(def-fns _ $ (many cmp-apart : (many (Nat) a b c d) -> (many (Rel) k) (erased (Ans k (RgSub (MkRg a b) (MkRg c d)) (RgDis (MkRg a b) (MkRg c d))) w))
  (match many (nat-cmp b c) _
    ((CLt _ _ _ _ l) (values (PDis) (AnsDis _ _ (DisLo a b c d l))))
    (else (match many (nat-cmp d a) _
      ((CLt _ _ _ _ u) (values (PDis) (AnsDis _ _ (DisHi a b c d u))))
      (else (values (PStr) (AnsStr _ _)))))))

(def-fns _ $ (many rg-cmp : (many (Rg) r q) -> (many (Rel) k) (erased (Ans k (RgSub r q) (RgDis r q)) w))
  (let-match many r (MkRg a b))
  (let-match many q (MkRg c d))
  (let-match many (le-dec c a) (LeY _ _ l) (else (cmp-apart a b c d)))
  (let-match many (le-dec b d) (LeY _ _ u) (else (cmp-apart a b c d)))
  (values (PSub) (AnsSub _ _ (MkRgSub a b c d l u))))

(def-fns _ $ (many rg-meet : (many (Rg) r q) -> (many (Rg) m) (erased (Weak r q m) w))
  (let-match many r (MkRg a b))
  (let-match many q (MkRg c d))
  (let ((many lo) (erased se))
    (match many (le-dec a c) (((Nat) lo) ((Or (Eq (Nat) lo a) (Eq (Nat) lo c)) se)) ((LeY _ _ _) (values c (OrR _ _ (Refl _ c)))) ((LeN _ _ _) (values a (OrL _ _ (Refl _ a))))))
  (let ((many hi) (erased sg))
    (match many (le-dec b d) (((Nat) hi) ((Or (Eq (Nat) hi b) (Eq (Nat) hi d)) sg)) ((LeY _ _ _) (values b (OrL _ _ (Refl _ b)))) ((LeN _ _ _) (values d (OrR _ _ (Refl _ d))))))
  (values (MkRg lo hi) (WkM a b c d lo hi se sg)))

(def-fns _ $ (many rel-meet : (erased Type Pa Na Pb Nb) (many (Rel) a) (erased (Ans a Pa Na) x) (many (Rel) b) (erased (Ans b Pb Nb) y)
    -> (many (Rel) k) (erased (Ans k (Both Pa Pb) (Or Na Nb)) z))
  (match many a _
    ((PDis) (let-match erased x (AnsDis _ _ n1)) (values (PDis) (AnsDis _ _ (OrL _ _ n1))))
    ((PSub)
      (let-match erased x (AnsSub _ _ p1))
      (match many b _
        ((PSub) (let-match erased y (AnsSub _ _ p2)) (values (PSub) (AnsSub _ _ (MkBoth _ _ p1 p2))))
        ((PDis) (let-match erased y (AnsDis _ _ n2)) (values (PDis) (AnsDis _ _ (OrR _ _ n2))))
        ((PStr) (values (PStr) (AnsStr _ _)))))
    ((PStr)
      (let-match many b (PDis) (else (values (PStr) (AnsStr _ _))))
      (let-match erased y (AnsDis _ _ n2))
      (values (PDis) (AnsDis _ _ (OrR _ _ n2))))))

; Generic lists matched entry by entry: ys is no longer than xs and each y is related to the x at its position (Pw), or
; some y is (Ex), or (Bad) some y is or ys is longer than xs.
(def-adts $ (Pw : (Type A) (Type B) ((TyCtor (A x) (B y) -> Type) R) ((List A) xs) ((List B) ys) -> Type)
  enum
  (many PwNil : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased (List A) xs) -> (Pw A B R xs (Nil B)))
  (many PwCons : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased B y) (erased (List A) xs)
      (erased (List B) ys) (erased (R x y) p) (erased (Pw A B R xs ys) rest) -> (Pw A B R (Cons A x xs) (Cons B y ys))))

(def-adts $ (Ex : (Type A) (Type B) ((TyCtor (A x) (B y) -> Type) R) ((List A) xs) ((List B) ys) -> Type)
  enum
  (many ExHere : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased B y) (erased (List A) xs)
      (erased (List B) ys) (erased (R x y) p) -> (Ex A B R (Cons A x xs) (Cons B y ys)))
  (many ExThere : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased B y) (erased (List A) xs)
      (erased (List B) ys) (erased (Ex A B R xs ys) rest) -> (Ex A B R (Cons A x xs) (Cons B y ys))))

(def-adts $ (Bad : (Type A) (Type B) ((TyCtor (A x) (B y) -> Type) R) ((List A) xs) ((List B) ys) -> Type)
  enum
  (many BadHere : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased B y) (erased (List A) xs)
      (erased (List B) ys) (erased (R x y) p) -> (Bad A B R (Cons A x xs) (Cons B y ys)))
  (many BadShort : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased B y) (erased (List B) ys)
      -> (Bad A B R (Nil A) (Cons B y ys)))
  (many BadThere : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased A x) (erased B y) (erased (List A) xs)
      (erased (List B) ys) (erased (Bad A B R xs ys) rest) -> (Bad A B R (Cons A x xs) (Cons B y ys))))

(def-fns _ $ (erased ex-bad : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R) (erased (List A) xs) (erased (List B) ys)
    (subterm erased (Ex A B R xs ys) e) -> (erased (Bad A B R xs ys) b))
  (match erased e _
    ((ExHere _ _ _ x y xs1 ys1 p) (BadHere A B R x y xs1 ys1 p))
    ((ExThere _ _ _ x y xs1 ys1 e1) (BadThere A B R x y xs1 ys1 (ex-bad A B R xs1 ys1 e1)))))

(def-fns _ $ (erased ans-cons : (erased Type A B) (erased (TyCtor (A x) (B y) -> Type) R S) (erased A x) (erased B y)
    (erased (List A) xs) (erased (List B) ys) (erased (Rel) k)
    (erased (Ans k (Both (R x y) (Pw A B R xs ys)) (Or (S x y) (Ex A B S xs ys))) w)
    -> (erased (Ans k (Pw A B R (Cons A x xs) (Cons B y ys)) (Ex A B S (Cons A x xs) (Cons B y ys))) r))
  (match erased w _
    ((AnsSub _ _ b) (let-match erased b (MkBoth _ _ p rest)) (AnsSub _ _ (PwCons A B R x y xs ys p rest)))
    ((AnsDis _ _ o)
      (match erased o _
        ((OrL _ _ d) (AnsDis _ _ (ExHere A B S x y xs ys d)))
        ((OrR _ _ e) (AnsDis _ _ (ExThere A B S x y xs ys e)))))
    ((AnsStr _ _) (AnsStr _ _))))

(def-adts $ (Sec : -> Type)
  enum
  (many MkSec : (many (Nat) a h) (many (List (Nat)) fs) -> (Sec)))

(def-adts $ (FitSec : ((Sec) o) ((Sub) x) -> Type)
  enum
  (many MkFitSec : (erased (Nat) a h) (erased (List (Nat)) as) (erased (Rg) s hr) (erased (List (Rg)) fs)
      (erased (InRg a s) p1) (erased (InRg h hr) p2) (erased (Pw (Nat) (Rg) InRg as fs) p3) -> (FitSec (MkSec a h as) (MkSub s hr fs))))

(def-adts $ (OutSec : ((Sec) o) ((Sub) x) -> Type)
  enum
  (many OSSpoke : (erased (Nat) a h) (erased (List (Nat)) as) (erased (Rg) s hr) (erased (List (Rg)) fs) (erased (OutRg a s) p)
      -> (OutSec (MkSec a h as) (MkSub s hr fs)))
  (many OSHat : (erased (Nat) a h) (erased (List (Nat)) as) (erased (Rg) s hr) (erased (List (Rg)) fs) (erased (OutRg h hr) p)
      -> (OutSec (MkSec a h as) (MkSub s hr fs)))
  (many OSFan : (erased (Nat) a h) (erased (List (Nat)) as) (erased (Rg) s hr) (erased (List (Rg)) fs)
      (erased (Bad (Nat) (Rg) OutRg as fs) p) -> (OutSec (MkSec a h as) (MkSub s hr fs))))

(def-adts $ (SubSub : ((Sub) x y) -> Type)
  enum
  (many MkSubSub : (erased (Rg) s h s2 h2) (erased (List (Rg)) fp fq)
      (erased (Both (RgSub s s2) (Both (RgSub h h2) (Pw (Rg) (Rg) RgSub fp fq))) p) -> (SubSub (MkSub s h fp) (MkSub s2 h2 fq))))

(def-adts $ (SubDis : ((Sub) x y) -> Type)
  enum
  (many MkSubDis : (erased (Rg) s h s2 h2) (erased (List (Rg)) fp fq)
      (erased (Or (RgDis s s2) (Or (RgDis h h2) (Ex (Rg) (Rg) RgDis fp fq))) p) -> (SubDis (MkSub s h fp) (MkSub s2 h2 fq))))

(def-fns _ $ (many fans-cmp : (subterm many (List (Rg)) fp) (many (List (Rg)) fq)
    -> (many (Rel) k) (erased (Ans k (Pw (Rg) (Rg) RgSub fp fq) (Ex (Rg) (Rg) RgDis fp fq)) w))
  (let-match many fq (Cons _ g gs) ((Nil _) (values (PSub) (AnsSub _ _ (PwNil _ _ RgSub fp)))))
  (let-match many fp (Cons _ f fs) ((Nil _) (values (PStr) (AnsStr _ _))))
  (let ((many k1) (erased w1)) (rg-cmp f g))
  (let ((many k2) (erased w2)) (notail $ fans-cmp fs gs))
  (let ((many k) (erased w)) (rel-meet _ _ _ _ k1 w1 k2 w2))
  (values k (ans-cons _ _ RgSub RgDis f g fs gs k w)))

(def-fns _ $ (many sub-cmp : (many (Sub) x y) -> (many (Rel) k) (erased (Ans k (SubSub x y) (SubDis x y)) w))
  (let-match many x (MkSub s h fp))
  (let-match many y (MkSub s2 h2 fq))
  (let ((many k1) (erased w1)) (rg-cmp s s2))
  (let ((many k2) (erased w2)) (rg-cmp h h2))
  (let ((many k3) (erased w3)) (fans-cmp fp fq))
  (let ((many k4) (erased w4)) (rel-meet _ _ _ _ k2 w2 k3 w3))
  (let ((many k) (erased w)) (rel-meet _ _ _ _ k1 w1 k4 w4))
  (values k (match erased w _
    ((AnsSub _ _ b) (AnsSub _ _ (MkSubSub s h s2 h2 fp fq b)))
    ((AnsDis _ _ o) (AnsDis _ _ (MkSubDis s h s2 h2 fp fq o)))
    ((AnsStr _ _) (AnsStr _ _)))))

(def-fns _ $ (many part-cmp : (subterm many (List (Sub)) p) (many (List (Sub)) q)
    -> (many (Rel) k) (erased (Ans k (Pw (Sub) (Sub) SubSub p q) (Ex (Sub) (Sub) SubDis p q)) w))
  (let-match many q (Cons _ y q1) ((Nil _) (values (PSub) (AnsSub _ _ (PwNil _ _ SubSub p)))))
  (let-match many p (Cons _ x p1) ((Nil _) (values (PStr) (AnsStr _ _))))
  (let ((many k1) (erased w1)) (sub-cmp x y))
  (let ((many k2) (erased w2)) (notail $ part-cmp p1 q1))
  (let ((many k) (erased w)) (rel-meet _ _ _ _ k1 w1 k2 w2))
  (values k (ans-cons _ _ SubSub SubDis x y p1 q1 k w)))

(def-fns _ $ (erased fans-sub : (erased (List (Nat)) as) (erased (List (Rg)) fp fq) (subterm erased (Pw (Nat) (Rg) InRg as fp) f)
    (erased (Pw (Rg) (Rg) RgSub fp fq) s) -> (erased (Pw (Nat) (Rg) InRg as fq) r))
  (let-match erased s (PwCons _ _ _ r q fp1 fq1 rs s1) ((PwNil _ _ _ _) (PwNil _ _ InRg as)))
  (let-match erased f (PwCons _ _ _ a _ as1 _ pa f1))
  (PwCons _ _ InRg a q as1 fq1 (rg-sub a r q pa rs) (fans-sub as1 fp1 fq1 f1 s1)))

(def-fns _ $ (erased fans-dis : (erased (List (Nat)) as) (erased (List (Rg)) fp fq) (subterm erased (Pw (Nat) (Rg) InRg as fp) f)
    (erased (Ex (Rg) (Rg) RgDis fp fq) d) -> (erased (Ex (Nat) (Rg) OutRg as fq) r))
  (let-match erased f (PwCons _ _ _ a r as1 fp1 pa f1) (absurd (PwNil _ _ _ _) d))
  (match erased d _
    ((ExHere _ _ _ _ q _ fq1 rd) (ExHere _ _ OutRg a q as1 fq1 (rg-dis a r q pa rd)))
    ((ExThere _ _ _ _ q _ fq1 d1) (ExThere _ _ OutRg a q as1 fq1 (fans-dis as1 fp1 fq1 f1 d1)))))

(def-fns _ $ (erased fans-bad : (erased (List (Nat)) as) (erased (List (Rg)) fs) (subterm erased (Pw (Nat) (Rg) InRg as fs) f)
    (erased (Bad (Nat) (Rg) OutRg as fs) b) -> (erased (False) r))
  (let-match erased f (PwCons _ _ _ a r as1 fs1 pa f1) (absurd (PwNil _ _ _ _) b))
  (match erased b _
    ((BadHere _ _ _ _ _ _ _ o) (in-out a r pa o))
    ((BadThere _ _ _ _ _ _ _ b1) (fans-bad as1 fs1 f1 b1))))

(def-fns _ $ (erased sec-sub : (erased (Sec) o) (erased (Sub) x y) (erased (FitSec o x) f) (erased (SubSub x y) s) -> (erased (FitSec o y) r))
  (let-match erased f (MkFitSec a h as sp hp fp p1 p2 p3))
  (let-match erased s (MkSubSub _ _ s2 h2 _ fq b))
  (let-match erased b (MkBoth _ _ bs b1))
  (let-match erased b1 (MkBoth _ _ bh bf))
  (MkFitSec a h as s2 h2 fq (rg-sub a sp s2 p1 bs) (rg-sub h hp h2 p2 bh) (fans-sub as fp fq p3 bf)))

(def-fns _ $ (erased sec-dis : (erased (Sec) o) (erased (Sub) x y) (erased (FitSec o x) f) (erased (SubDis x y) s) -> (erased (OutSec o y) r))
  (let-match erased f (MkFitSec a h as sp hp fp p1 p2 p3))
  (let-match erased s (MkSubDis _ _ s2 h2 _ fq d))
  (let-match erased d (OrR _ _ d1) ((OrL _ _ ds) (OSSpoke a h as s2 h2 fq (rg-dis a sp s2 p1 ds))))
  (let-match erased d1 (OrR _ _ df) ((OrL _ _ dh) (OSHat a h as s2 h2 fq (rg-dis h hp h2 p2 dh))))
  (OSFan a h as s2 h2 fq (ex-bad _ _ OutRg as fq (fans-dis as fp fq p3 df))))

(def-fns _ $ (erased sec-out : (erased (Sec) o) (erased (Sub) x) (erased (FitSec o x) f) (erased (OutSec o x) b) -> (erased (False) r))
  (let-match erased f (MkFitSec a h as sp hp fp p1 p2 p3))
  (match erased b _
    ((OSSpoke _ _ _ _ _ _ q) (in-out a sp p1 q))
    ((OSHat _ _ _ _ _ _ q) (in-out h hp p2 q))
    ((OSFan _ _ _ _ _ _ q) (fans-bad as fp p3 q))))

(def-fns _ $ (erased fit-sub : (erased (List (Sec)) os) (erased (List (Sub)) p q) (subterm erased (Pw (Sec) (Sub) FitSec os p) f)
    (erased (Pw (Sub) (Sub) SubSub p q) s) -> (erased (Pw (Sec) (Sub) FitSec os q) r))
  (let-match erased s (PwCons _ _ _ x y p1 q1 sx s1) ((PwNil _ _ _ _) (PwNil _ _ FitSec os)))
  (let-match erased f (PwCons _ _ _ o _ os1 _ fo f1))
  (PwCons _ _ FitSec o y os1 q1 (sec-sub o x y fo sx) (fit-sub os1 p1 q1 f1 s1)))

(def-fns _ $ (erased fit-dis : (erased (List (Sec)) os) (erased (List (Sub)) p q) (subterm erased (Pw (Sec) (Sub) FitSec os p) f)
    (erased (Ex (Sub) (Sub) SubDis p q) d) -> (erased (Bad (Sec) (Sub) OutSec os q) r))
  (let-match erased f (PwCons _ _ _ o x os1 p1 fo f1) (absurd (PwNil _ _ _ _) d))
  (match erased d _
    ((ExHere _ _ _ _ y _ q1 dx) (BadHere _ _ OutSec o y os1 q1 (sec-dis o x y fo dx)))
    ((ExThere _ _ _ _ y _ q1 d1) (BadThere _ _ OutSec o y os1 q1 (fit-dis os1 p1 q1 f1 d1)))))

(def-fns _ $ (erased fit-bad : (erased (List (Sec)) os) (erased (List (Sub)) p) (subterm erased (Pw (Sec) (Sub) FitSec os p) f)
    (erased (Bad (Sec) (Sub) OutSec os p) b) -> (erased (False) r))
  (let-match erased f (PwCons _ _ _ o x os1 p1 fo f1) (absurd (PwNil _ _ _ _) b))
  (match erased b _
    ((BadHere _ _ _ _ _ _ _ q) (sec-out o x fo q))
    ((BadThere _ _ _ _ _ _ _ b1) (fit-bad os1 p1 f1 b1))))
