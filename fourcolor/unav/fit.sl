; Certified part semantics after part.v, over the types of part.sl. A part is read against Obs, the arities seen around
; a hub dart: per sector the spoke arity a, the hat arity h and the fan arities, so that everything here is about lists
; and numbers; map.sl ties Obs to a hypermap. A range MkRg lo hi holds an arity whose value clamped at 9 lies in [lo, hi].

(unary 4)
(unary 5 4)
(unary 6 5)
(unary 7 6)
(unary 8 7)
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

(def-adts $ (FansMeet : ((List (Rg)) fp fq fm) -> Type)
  enum
  (many FMNilL : (erased (List (Rg)) fq) -> (FansMeet (Nil (Rg)) fq fq))
  (many FMNilR : (erased (List (Rg)) fp) -> (FansMeet fp (Nil (Rg)) fp))
  (many FMCons : (erased (Rg) f g h) (erased (List (Rg)) fs gs hs) (erased (Weak f g h) w) (erased (FansMeet fs gs hs) rest)
      -> (FansMeet (Cons (Rg) f fs) (Cons (Rg) g gs) (Cons (Rg) h hs))))

(def-adts $ (SubMeet : ((Sub) x y z) -> Type)
  enum
  (many MkSubMeet : (erased (Rg) s h s2 h2 s3 h3) (erased (List (Rg)) fp fq fm) (erased (Weak s s2 s3) ws) (erased (Weak h h2 h3) wh)
      (erased (FansMeet fp fq fm) wf) -> (SubMeet (MkSub s h fp) (MkSub s2 h2 fq) (MkSub s3 h3 fm))))

(def-adts $ (PartMeet : ((List (Sub)) p q m) -> Type)
  enum
  (many PMKeep : (erased (List (Sub)) p q) -> (PartMeet p q p))
  (many PMCons : (erased (Sub) x y z) (erased (List (Sub)) p q m) (erased (SubMeet x y z) w) (erased (PartMeet p q m) rest)
      -> (PartMeet (Cons (Sub) x p) (Cons (Sub) y q) (Cons (Sub) z m))))

(def-fns _ $ (many fans-meet : (subterm many (List (Rg)) fp) (many (List (Rg)) fq) -> (many (List (Rg)) fm) (erased (FansMeet fp fq fm) w))
  (let-match many fp (Cons _ f fs) ((Nil _) (values fq (FMNilL fq))))
  (let-match many fq (Cons _ g gs) ((Nil _) (values fp (FMNilR fp))))
  (let ((many h) (erased w1)) (rg-meet f g))
  (let ((many hs) (erased w2)) (notail $ fans-meet fs gs))
  (values (Cons _ h hs) (FMCons f g h fs gs hs w1 w2)))

(def-fns _ $ (many part-meet : (many (List (Sub)) p) (subterm many (List (Sub)) q) -> (many (List (Sub)) m) (erased (PartMeet p q m) w))
  (let-match many q (Cons _ y q1) ((Nil _) (values p (PMKeep p q))))
  (let-match many p (Cons _ x p1) ((Nil _) (values p (PMKeep p q))))
  (let-match many x (MkSub s h fp))
  (let-match many y (MkSub s2 h2 fq))
  (let ((many fpe) (many fqe)) (values (nilp _ fp) (nilp _ fq)))
  (let-match many (and (negb fpe) (negb fqe) (negb (nat-eqb (size _ fp) (size _ fq)))) (BFalse) ((BTrue) (values p (PMKeep p q))))
  (let ((many s3) (erased ws))
    (match many fpe (((Rg) s3) ((Weak s s2 s3) ws))
      ((BTrue) (match many fqe (((Rg) s3) ((Weak s s2 s3) ws)) ((BTrue) (rg-meet s s2)) ((BFalse) (values s2 (WkR s s2)))))
      ((BFalse) (values s (WkL s s2)))))
  (let ((many h3) (erased wh)) (rg-meet h h2))
  (let ((many fm) (erased wf)) (fans-meet fp fq))
  (let ((many m1) (erased w1)) (notail $ part-meet p1 q1))
  (values (Cons _ (MkSub s3 h3 fm) m1) (PMCons x y (MkSub s3 h3 fm) p1 q1 m1 (MkSubMeet s h s2 h2 s3 h3 fp fq fm ws wh wf) w1)))

(def-fns _ $ (erased fans-meet-fit : (erased (List (Nat)) as) (erased (List (Rg)) fp fq fm) (erased (Pw (Nat) (Rg) InRg as fp) f)
    (erased (Pw (Nat) (Rg) InRg as fq) g) (subterm erased (FansMeet fp fq fm) w) -> (erased (Pw (Nat) (Rg) InRg as fm) r))
  (let-match erased w (FMCons r1 r2 r3 fs gs hs wr w1) ((FMNilL _) g) ((FMNilR _) f))
  (let-match erased f (PwCons _ _ _ a _ as1 _ pa f1))
  (let-match erased g (PwCons _ _ _ _ _ _ _ pb g1))
  (PwCons _ _ InRg a r3 as1 hs (rg-weak a r1 r2 r3 pa pb wr) (fans-meet-fit as1 fs gs hs f1 g1 w1)))

(def-fns _ $ (erased fit-meet : (erased (List (Sec)) os) (erased (List (Sub)) p q m) (erased (Pw (Sec) (Sub) FitSec os p) f)
    (erased (Pw (Sec) (Sub) FitSec os q) g) (subterm erased (PartMeet p q m) w) -> (erased (Pw (Sec) (Sub) FitSec os m) r))
  (let-match erased w (PMCons x y z p1 q1 m1 wz w1) ((PMKeep _ _) f))
  (let-match erased f (PwCons _ _ _ o _ os1 _ fo f1))
  (let-match erased g (PwCons _ _ _ _ _ _ _ go g1))
  (let-match erased fo (MkFitSec a h as s hr fp ps ph pfa))
  (let-match erased go (MkFitSec _ _ _ s2 h2 fq qs qh qf))
  (let-match erased wz (MkSubMeet _ _ _ _ s3 h3 _ _ fm ws wh wf))
  (PwCons _ _ FitSec o z os1 m1
    (MkFitSec a h as s3 h3 fm (rg-weak a s s2 s3 ps qs ws) (rg-weak h hr h2 h3 ph qh wh) (fans-meet-fit as fp fq fm pfa qf wf))
    (fit-meet os1 p1 q1 m1 f1 g1 w1)))

(def-adts $ (All : (Type A) ((TyCtor (A x) -> Type) P) ((List A) xs) -> Type)
  enum
  (many AllNil : (erased Type A) (erased (TyCtor (A x) -> Type) P) -> (All A P (Nil A)))
  (many AllCons : (erased Type A) (erased (TyCtor (A x) -> Type) P) (erased A x) (erased (List A) xs) (erased (P x) p)
      (erased (All A P xs) rest) -> (All A P (Cons A x xs))))

(def-adts $ (Pent : ((Nat) a) -> Type)
  enum
  (many MkPent : (erased (Nat) a) (erased (Lt 4 a) p) -> (Pent a)))

; A sector as a pentagonal map has it: arities at least 5, and one fan per spoke dart past the fifth.
(def-adts $ (SecOk : ((Sec) o) -> Type)
  enum
  (many MkSecOk : (erased (Nat) a h n) (erased (List (Nat)) as) (erased (Lt 4 a) pa) (erased (Lt 4 h) ph) (erased (All (Nat) Pent as) pv)
      (erased (Length (Nat) as n) l) (erased (Add 5 n a) e) -> (SecOk (MkSec a h as))))

(def-adts $ (Monus : ((Nat) a b r) -> Type)
  enum
  (many MoAdd : (erased (Nat) a b r) (erased (Add b r a) p) -> (Monus a b r))
  (many MoNeg : (erased (Nat) a b) (erased (Lt a b) p) -> (Monus a b (Zero))))

(def-fns _ $ (many monus-c : (subterm many (Nat) a) (many (Nat) b) -> (many (Nat) r) (erased (Monus a b r) w))
  (let-match many b (Succ b1) ((Zero) (values a (MoAdd a (Zero) a (AddZero a)))))
  (let-match many a (Succ a1) ((Zero) (values (Zero) (MoNeg (Zero) b (LtZ b1)))))
  (let ((many r) (erased w1)) (tail $ monus-c a1 b1))
  (values r (match erased w1 _ ((MoAdd _ _ _ p) (MoAdd a b r (AddSucc b1 r a1 p))) ((MoNeg _ _ p) (MoNeg a b (LtS a1 b1 p))))))

(def-fns _ $ (many nseq-c : (erased Type A) (subterm many (Nat) n) (many A x) -> (many (List A) ys) (erased (Repeat A n x ys) p))
  (let-match many n (Succ n1) ((Zero) (values (Nil _) (RepeatNil _ x))))
  (let ((many ys) (erased p)) (notail $ nseq-c _ n1 x))
  (values (Cons _ x ys) (RepeatCons _ n1 x ys p)))

(def-fns _ $ (erased add-inj : (erased (Nat) a b c d) (subterm erased (Add a b c) p) (erased (Add a d c) q) -> (erased (Eq (Nat) b d) e))
  (let-match erased p (AddSucc a1 _ c1 p1) ((AddZero _) (let-match erased q (AddZero _)) (Refl _ b)))
  (let-match erased q (AddSucc _ _ _ q1))
  (add-inj a1 b c1 d p1 q1))

(def-fns _ $ (erased le-antisym : (erased (Nat) a b) (erased (Lt a (Succ b)) p) (erased (Lt b (Succ a)) q) -> (erased (Eq (Nat) a b) e))
  (match erased (nat-cmp a b) _
    (absurd (CLt _ _ _ _ l) (lt-le-absurd a b l q))
    ((CEq _ _ _) (Refl _ a))
    (absurd (CGt _ _ _ _ l) (lt-le-absurd b a l p))))

(def-fns _ $ (erased clamp-le9 : (erased (Nat) a m) (erased (Clamp a m) c) -> (erased (Lt m (Succ 9)) r))
  (match erased c _ ((ClLo _ p) (lt-weaken a 9 p)) ((ClHi _ _) (lt-succ 9))))

(def-fns _ $ (erased clamp-ge5 : (erased (Nat) a m) (erased (Clamp a m) c) (erased (Lt 4 a) pa) -> (erased (Lt 4 m) r))
  (match erased c _ ((ClLo _ _) pa) ((ClHi _ _) (lt-trans 4 8 9 (prove-literal-lt 4 8) (lt-succ 8)))))

(def-fns _ $ (erased in59 : (erased (Nat) a) (erased (Lt 4 a) pa) -> (erased (InRg a (MkRg 5 9)) r))
  (let ((erased m) (erased c)) (clamp-exists a))
  (MkInRg a m 5 9 c (LtS 4 m (clamp-ge5 a m c pa)) (clamp-le9 a m c)))

(def-adts $ (PSplit : ((Nat) k) ((Rg) lo hi) -> Type)
  enum
  (many PSIn : (erased (Nat) k) (erased (Lt 4 k) l) (erased (Lt k 9) u) -> (PSplit k (MkRg 5 k) (MkRg (Succ k) 9)))
  (many PSOut : (erased (Nat) k) -> (PSplit k (MkRg 5 9) (MkRg 5 9))))

(def-fns _ $ (many prange : (many (Nat) k) -> (many (Rg) lo hi) (erased (PSplit k lo hi) s))
  (let-match many (nat-cmp 4 k) (CLt _ _ _ _ l) (else (values r59 r59 (PSOut k))))
  (let-match many (nat-cmp k 9) (CLt _ _ _ _ u) (else (values r59 r59 (PSOut k))))
  (values (MkRg 5 k) (MkRg (Succ k) 9) (PSIn k l u)))

(def-fns _ $ (erased psplit-cover : (erased (Nat) k a) (erased (Rg) lo hi) (erased (PSplit k lo hi) s) (erased (Lt 4 a) pa)
    -> (erased (Or (InRg a lo) (InRg a hi)) r))
  (let ((erased m) (erased c)) (clamp-exists a))
  (let ((erased l5) (erased l9)) (values (LtS 4 m (clamp-ge5 a m c pa)) (clamp-le9 a m c)))
  (let-match erased s (PSIn _ _ _) ((PSOut _) (OrL _ _ (MkInRg a m 5 9 c l5 l9))))
  (match erased (le-dec m k) _
    ((LeY _ _ p) (OrL _ _ (MkInRg a m 5 k c l5 p)))
    ((LeN _ _ p) (OrR _ _ (MkInRg a m (Succ k) 9 c (LtS k m p) l9)))))

(def-adts $ (RgSplit : ((Nat) k) ((Rg) r zl zh) -> Type)
  enum
  (many MkRgSplit : (erased (Nat) k) (erased (Rg) r lo hi zl zh) (erased (PSplit k lo hi) s) (erased (Weak lo r zl) wl)
      (erased (Weak hi r zh) wh) -> (RgSplit k r zl zh)))

(def-fns _ $ (many rg-split : (many (Nat) k) (many (Rg) r) -> (many (Rg) zl zh) (erased (RgSplit k r zl zh) w))
  (let ((many lo) (many hi) (erased s)) (prange k))
  (let ((many zl) (erased wl)) (rg-meet lo r))
  (let ((many zh) (erased wh)) (rg-meet hi r))
  (values zl zh (MkRgSplit k r lo hi zl zh s wl wh)))

(def-fns _ $ (erased rg-split-cover : (erased (Nat) k a) (erased (Rg) r zl zh) (erased (InRg a r) p) (erased (Lt 4 a) pa)
    (erased (RgSplit k r zl zh) w) -> (erased (Or (InRg a zl) (InRg a zh)) o))
  (let-match erased w (MkRgSplit _ _ lo hi _ _ s wl wh))
  (match erased (psplit-cover k a lo hi s pa) _
    ((OrL _ _ q) (OrL _ _ (rg-weak a lo r zl q p wl)))
    ((OrR _ _ q) (OrR _ _ (rg-weak a hi r zh q p wh)))))

(def-adts $ (RgAt : ((List (Rg)) xs) ((Nat) i) -> Type)
  enum
  (many RAHit : (erased (List (Rg)) xs) (erased (Nat) i) (many (Rg) r) (erased (Nth (Rg) xs i r) p) -> (RgAt xs i))
  (many RAMiss : (erased (List (Rg)) xs) (erased (Nat) i) -> (RgAt xs i)))

(def-fns _ $ (many rg-at : (subterm many (Nat) i) (many (List (Rg)) xs) -> (many (RgAt xs i) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (RAMiss xs i)))
  (let-match many i (Succ i1) ((Zero) (RAHit xs i x (NthHere _ x rest))))
  (let-match many (notail $ rg-at i1 rest) (RAHit _ _ r p) ((RAMiss _ _) (RAMiss xs i)))
  (RAHit xs i r (NthThere _ x rest i1 r p)))

(def-fns _ $ (many rg-set : (subterm many (Nat) i) (many (Rg) y) (many (List (Rg)) xs) (erased (Rg) x) (erased (Nth (Rg) xs i x) p)
    -> (many (List (Rg)) ys) (erased (SetNth (Rg) xs i y ys) s))
  (let-match many xs (Cons _ z rest) (absurd (Nil _) p))
  (let-match many i (Succ i1) ((Zero) (values (Cons _ y rest) (SetHere _ z y rest))))
  (let-match erased p (NthThere _ _ _ _ _ p1))
  (let ((many ys) (erased s)) (notail $ rg-set i1 y rest x p1))
  (values (Cons _ z ys) (SetThere _ z rest i1 y ys s)))

(def-adts $ (Expand : ((Sub) x) ((List (Rg)) gs) -> Type)
  enum
  (many ExpKeep : (erased (Rg) s h) (erased (List (Rg)) fs) -> (Expand (MkSub s h fs) fs))
  (many ExpFill : (erased (Nat) b n) (erased (Rg) h) (erased (List (Rg)) gs) (erased (Lt b 9) u) (erased (Monus b 5 n) mo)
      (erased (Repeat (Rg) n (MkRg 5 9) gs) rp) -> (Expand (MkSub (MkRg b b) h (Nil (Rg))) gs)))

(def-fns _ $ (many expand : (many (Sub) x) -> (many (List (Rg)) gs) (erased (Expand x gs) w))
  (let-match many x (MkSub s h fs))
  (let-match many fs (Nil _) (else (values fs (ExpKeep s h fs))))
  (let-match many s (MkRg a b))
  (let-match many (nat-eq a b) (Equal _ _ _) (else (values fs (ExpKeep s h fs))))
  (let-match many (le-dec b 8) (LeY _ _ u) (else (values fs (ExpKeep s h fs))))
  (let ((many n) (erased mo)) (monus-c b 5))
  (let ((many gs) (erased rp)) (nseq-c _ n r59))
  (values gs (ExpFill b n h gs u mo rp)))

(def-fns _ $ (erased repeat-fit : (erased (Nat) n) (erased (List (Nat)) as) (erased (List (Rg)) gs) (subterm erased (Repeat (Rg) n (MkRg 5 9) gs) rp)
    (erased (Length (Nat) as n) l) (erased (All (Nat) Pent as) pv) -> (erased (Pw (Nat) (Rg) InRg as gs) r))
  (let-match erased rp (RepeatCons _ n1 _ gs1 rp1) ((RepeatNil _ _) (PwNil _ _ InRg as)))
  (let-match erased l (LengthCons _ a as1 _ l1))
  (let-match erased pv (AllCons _ _ _ _ pa pv1))
  (let-match erased pa (MkPent _ q))
  (PwCons _ _ InRg a (MkRg 5 9) as1 gs1 (in59 a q) (repeat-fit n1 as1 gs1 rp1 l1 pv1)))

(def-fns _ $ (erased expand-fit : (erased (Nat) a h) (erased (List (Nat)) as) (erased (Sub) x) (erased (List (Rg)) gs)
    (erased (FitSec (MkSec a h as) x) f) (erased (SecOk (MkSec a h as)) ok) (erased (Expand x gs) w) -> (erased (Pw (Nat) (Rg) InRg as gs) r))
  (let-match erased f (MkFitSec _ _ _ s hr fs ps ph pfs))
  (let-match erased w (ExpFill b n _ _ u mo rp) ((ExpKeep _ _ _) pfs))
  (let-match erased ok (MkSecOk _ _ n2 _ pa _ pfv l e))
  (let-match erased ps (MkInRg _ m _ _ c l1 u1))
  (let-match erased (le-antisym b m l1 u1) (Refl _ _))
  (let-match erased c (ClLo _ _) (absurd (ClHi _ _) (lt-irrefl 9 u)))
  (let-match erased mo (MoAdd _ _ _ e2) (absurd (MoNeg _ _ lb) (lt-le-absurd 4 a pa lb)))
  (let-match erased (add-inj 5 n a n2 e2 e) (Refl _ _))
  (repeat-fit n as gs rp l pfv))

(def-fns _ $ (erased fans-split : (erased (Nat) k i) (erased (List (Nat)) as) (erased (Rg) r rl rh) (erased (List (Rg)) gs gl gh)
    (erased (Pw (Nat) (Rg) InRg as gs) f) (erased (All (Nat) Pent as) pv) (subterm erased (Nth (Rg) gs i r) nr) (erased (RgSplit k r rl rh) w)
    (erased (SetNth (Rg) gs i rl gl) sl) (erased (SetNth (Rg) gs i rh gh) sh) -> (erased (Or (Pw (Nat) (Rg) InRg as gl) (Pw (Nat) (Rg) InRg as gh)) o))
  (let-match erased f (PwCons _ _ _ a _ as1 gs1 pa f1) (absurd (PwNil _ _ _ _) nr))
  (let-match erased pv (AllCons _ _ _ _ pent pv1))
  (match erased nr _
    ((NthHere _ _ _)
      (let-match erased sl (SetHere _ _ _ _))
      (let-match erased sh (SetHere _ _ _ _))
      (let-match erased pent (MkPent _ q))
      (match erased (rg-split-cover k a r rl rh pa q w) _
        ((OrL _ _ ql) (OrL _ _ (PwCons _ _ InRg a rl as1 gs1 ql f1)))
        ((OrR _ _ qh) (OrR _ _ (PwCons _ _ InRg a rh as1 gs1 qh f1)))))
    ((NthThere _ g _ i1 _ nr1)
      (let-match erased sl (SetThere _ _ _ _ _ gl1 sl1))
      (let-match erased sh (SetThere _ _ _ _ _ gh1 sh1))
      (match erased (fans-split k i1 as1 r rl rh gs1 gl1 gh1 f1 pv1 nr1 w sl1 sh1) _
        ((OrL _ _ ql) (OrL _ _ (PwCons _ _ InRg a g as1 gl1 pa ql)))
        ((OrR _ _ qh) (OrR _ _ (PwCons _ _ InRg a g as1 gh1 pa qh)))))))

(def-adts $ (SubSplit : ((Nat) k) ((Sub) x zl zh) -> Type)
  enum
  (many SSKeep : (erased (Nat) k) (erased (Sub) x) -> (SubSplit k x x x))
  (many SSSpoke : (erased (Nat) k) (erased (Rg) s h sl sh) (erased (RgSplit k s sl sh) w)
      -> (SubSplit k (MkSub s h (Nil (Rg))) (MkSub sl h (Nil (Rg))) (MkSub sh h (Nil (Rg)))))
  (many SSHat : (erased (Nat) k) (erased (Rg) s h hl hh) (erased (List (Rg)) fs) (erased (RgSplit k h hl hh) w)
      -> (SubSplit k (MkSub s h fs) (MkSub s hl fs) (MkSub s hh fs)))
  (many SSFan : (erased (Nat) k i) (erased (Rg) s h r rl rh) (erased (List (Rg)) fs gs gl gh) (erased (Expand (MkSub s h fs) gs) e)
      (erased (Nth (Rg) gs i r) nr) (erased (RgSplit k r rl rh) w) (erased (SetNth (Rg) gs i rl gl) sl) (erased (SetNth (Rg) gs i rh gh) sh)
      -> (SubSplit k (MkSub s h fs) (MkSub s h gl) (MkSub s h gh))))

(def-fns _ $ (many sub-split : (many (Loc) i) (many (Nat) k) (many (Sub) x) -> (many (Sub) zl zh) (erased (SubSplit k x zl zh) w))
  (let-match many x (MkSub s h fs))
  (match many i _
    ((LSpoke)
      (let-match many fs (Nil _) (else (values x x (SSKeep k x))))
      (let ((many sl) (many sh) (erased w)) (rg-split k s))
      (values (MkSub sl h fs) (MkSub sh h fs) (SSSpoke k s h sl sh w)))
    ((LHat) (let ((many hl) (many hh) (erased w)) (rg-split k h)) (values (MkSub s hl fs) (MkSub s hh fs) (SSHat k s h hl hh fs w)))
    ((LFan j)
      (let ((many gs) (erased e)) (expand x))
      (let-match many (rg-at j gs) (RAHit _ _ r nr) ((RAMiss _ _) (values x x (SSKeep k x))))
      (let ((many rl) (many rh) (erased w)) (rg-split k r))
      (let ((many gl) (erased sl)) (rg-set j rl gs r nr))
      (let ((many gh) (erased sh)) (rg-set j rh gs r nr))
      (values (MkSub s h gl) (MkSub s h gh) (SSFan k j s h r rl rh fs gs gl gh e nr w sl sh)))))

(def-fns _ $ (erased sub-split-cover : (erased (Nat) k) (erased (Sec) o) (erased (Sub) x zl zh) (erased (FitSec o x) f) (erased (SecOk o) ok)
    (erased (SubSplit k x zl zh) w) -> (erased (Or (FitSec o zl) (FitSec o zh)) r))
  (let-match erased f (MkFitSec a h as s hr fs ps ph pfs))
  (let-match erased ok (MkSecOk _ _ _ _ pa phh pfv _ _))
  (match erased w _
    ((SSKeep _ _) (OrL _ _ f))
    ((SSSpoke _ _ _ sl sh ws)
      (match erased (rg-split-cover k a s sl sh ps pa ws) _
        ((OrL _ _ q) (OrL _ _ (MkFitSec a h as sl hr fs q ph pfs)))
        ((OrR _ _ q) (OrR _ _ (MkFitSec a h as sh hr fs q ph pfs)))))
    ((SSHat _ _ _ hl hh _ wh)
      (match erased (rg-split-cover k h hr hl hh ph phh wh) _
        ((OrL _ _ q) (OrL _ _ (MkFitSec a h as s hl fs ps q pfs)))
        ((OrR _ _ q) (OrR _ _ (MkFitSec a h as s hh fs ps q pfs)))))
    ((SSFan _ i _ _ r rl rh _ gs gl gh e nr wr sl sh)
      (match erased (fans-split k i as r rl rh gs gl gh (expand-fit a h as x gs f ok e) pfv nr wr sl sh) _
        ((OrL _ _ q) (OrL _ _ (MkFitSec a h as s hr gl ps ph q)))
        ((OrR _ _ q) (OrR _ _ (MkFitSec a h as s hr gh ps ph q)))))))

(def-adts $ (PartSplit : ((Nat) k) ((List (Sub)) p ql qh) -> Type)
  enum
  (many PSKeep : (erased (Nat) k) (erased (List (Sub)) p) -> (PartSplit k p p p))
  (many PSHere : (erased (Nat) k) (erased (Sub) x zl zh) (erased (List (Sub)) p) (erased (SubSplit k x zl zh) w)
      -> (PartSplit k (Cons (Sub) x p) (Cons (Sub) zl p) (Cons (Sub) zh p)))
  (many PSThere : (erased (Nat) k) (erased (Sub) x) (erased (List (Sub)) p ql qh) (erased (PartSplit k p ql qh) w)
      -> (PartSplit k (Cons (Sub) x p) (Cons (Sub) x ql) (Cons (Sub) x qh))))

; Both halves of split_part at once: ql takes the arities up to k at location i of sector j, qh the others.
(def-fns _ $ (many split-both : (many (Loc) i) (subterm many (Nat) j) (many (Nat) k) (many (List (Sub)) p)
    -> (many (List (Sub)) ql qh) (erased (PartSplit k p ql qh) w))
  (let-match many p (Cons _ x rest) ((Nil _) (values p p (PSKeep k p))))
  (let-match many j (Succ j1)
    ((Zero)
      (let ((many zl) (many zh) (erased w)) (sub-split i k x))
      (values (Cons _ zl rest) (Cons _ zh rest) (PSHere k x zl zh rest w))))
  (let ((many ql) (many qh) (erased w)) (notail $ split-both i j1 k rest))
  (values (Cons _ x ql) (Cons _ x qh) (PSThere k x rest ql qh w)))

(def-fns _ $ (erased split-cover : (erased (Nat) k) (erased (List (Sec)) os) (erased (List (Sub)) p ql qh) (erased (Pw (Sec) (Sub) FitSec os p) f)
    (erased (All (Sec) SecOk os) ok) (subterm erased (PartSplit k p ql qh) w)
    -> (erased (Or (Pw (Sec) (Sub) FitSec os ql) (Pw (Sec) (Sub) FitSec os qh)) r))
  (match erased w _
    ((PSKeep _ _) (OrL _ _ f))
    ((PSHere _ x zl zh p1 wx)
      (let-match erased f (PwCons _ _ _ o _ os1 _ fo f1))
      (let-match erased ok (AllCons _ _ _ _ oko _))
      (match erased (sub-split-cover k o x zl zh fo oko wx) _
        ((OrL _ _ q) (OrL _ _ (PwCons _ _ FitSec o zl os1 p1 q f1)))
        ((OrR _ _ q) (OrR _ _ (PwCons _ _ FitSec o zh os1 p1 q f1)))))
    ((PSThere _ x p1 ql1 qh1 w1)
      (let-match erased f (PwCons _ _ _ o _ os1 _ fo f1))
      (let-match erased ok (AllCons _ _ _ _ _ ok1))
      (match erased (split-cover k os1 p1 ql1 qh1 f1 ok1 w1) _
        ((OrL _ _ q) (OrL _ _ (PwCons _ _ FitSec o x os1 ql1 fo q)))
        ((OrR _ _ q) (OrR _ _ (PwCons _ _ FitSec o x os1 qh1 fo q)))))))
