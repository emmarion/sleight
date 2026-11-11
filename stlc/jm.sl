(def-adts
  ((SNe : ((List (Ty)) g) ((Term) t) ((Ty) a) -> Type)
    enum
    (many NeVar : (erased (List (Ty)) g) (erased (Nat) i) (erased (Ty) a) (erased (Nth (Ty) g i a) p) -> (SNe g (Var i) a))
    (many NeApp : (erased (List (Ty)) g) (erased (Term) n u) (erased (Ty) a c) (erased (SNe g n (Arr a c)) p) (erased (SN g u a) q)
       -> (SNe g (App n u) c)))
  ((SN : ((List (Ty)) g) ((Term) t) ((Ty) a) -> Type)
    enum
    (many SNNe : (erased (List (Ty)) g) (erased (Term) t) (erased (Ty) a) (erased (SNe g t a) p) -> (SN g t a))
    (many SNLam : (erased (List (Ty)) g) (erased (Term) b) (erased (Ty) a c) (erased (SN (Cons (Ty) a g) b c) p) -> (SN g (Lam b) (Arr a c)))
    (many SNExp : (erased (List (Ty)) g) (erased (Term) t r) (erased (Ty) a) (erased (SNRed g t r a) p) (erased (SN g r a) q) -> (SN g t a)))
  ((SNRed : ((List (Ty)) g) ((Term) t) ((Term) r) ((Ty) a) -> Type)
    enum
    (many RdBeta : (erased (List (Ty)) g) (erased (Term) b u r) (erased (Ty) a c) (erased (SN g u a) p) (erased (Sub (Zero) u b r) q)
       -> (SNRed g (App (Lam b) u) r c))
    (many RdApp : (erased (List (Ty)) g) (erased (Term) t r w) (erased (Ty) a c) (erased (SNRed g t r (Arr a c)) p)
       -> (SNRed g (App t w) (App r w) c))))

(def-fns _
  ((erased wk-sn : (erased (List (Ty)) g h) (erased (Nat) k) (erased (Ty) b) (erased (Ins k b g h) ins)
      (erased (Term) t t2) (erased (Ty) a) (subterm erased (SN g t a) d) (erased (Shift k t t2) sh) -> (erased (SN h t2 a) e))
    (match erased d _
      ((SNNe _ _ _ p) (SNNe h t2 a (wk-ne g h k b ins t t2 a p sh)))
      ((SNLam _ t1 a1 c p)
        (let-match erased sh (ShLam _ _ t3 sh1))
        (SNLam h t3 a1 c (wk-sn (Cons _ a1 g) (Cons _ a1 h) (Succ k) b (InsS k b a1 g h ins) t1 t3 c p sh1)))
      ((SNExp _ _ r _ p q)
        (let ((erased r2) (erased sh2) (erased p2)) (wk-red g h k b ins t r t2 a p sh))
        (SNExp h t2 r2 a p2 (wk-sn g h k b ins r r2 a q sh2)))))
  ((erased wk-ne : (erased (List (Ty)) g h) (erased (Nat) k) (erased (Ty) b) (erased (Ins k b g h) ins)
      (erased (Term) t t2) (erased (Ty) a) (subterm erased (SNe g t a) d) (erased (Shift k t t2) sh) -> (erased (SNe h t2 a) e))
    (match erased d _
      ((NeVar _ i _ p) (let-match erased sh (ShVar _ _ j s)) (NeVar h j a (ins-fwd k b g h ins i j s a p)))
      ((NeApp _ n u a1 _ p q)
        (let-match erased sh (ShApp _ _ n2 _ u2 s1 s2))
        (NeApp h n2 u2 a1 a (wk-ne g h k b ins n n2 (Arr a1 a) p s1) (wk-sn g h k b ins u u2 a1 q s2)))))
  ((erased wk-red : (erased (List (Ty)) g h) (erased (Nat) k) (erased (Ty) b) (erased (Ins k b g h) ins)
      (erased (Term) t r t2) (erased (Ty) a) (subterm erased (SNRed g t r a) d) (erased (Shift k t t2) sh)
      -> (erased (Term) r2) (erased (Shift k r r2) e) (erased (SNRed h t2 r2 a) f))
    (match erased d _
      ((RdBeta _ t1 u _ a1 _ p q)
        (let-match erased sh (ShApp _ _ _ _ u2 s1 s2))
        (let-match erased s1 (ShLam _ _ t3 s3))
        (let ((erased r2) (erased e) (erased f)) (shift-sub (Zero) k u t1 r t3 u2 q s3 s2 (LtZ k)))
        (values r2 e (RdBeta h t3 u2 r2 a1 a (wk-sn g h k b ins u u2 a1 p s2) f)))
      ((RdApp _ t1 r1 w a1 _ p)
        (let-match erased sh (ShApp _ _ t3 _ w2 s1 s2))
        (let ((erased r2) (erased e) (erased f)) (wk-red g h k b ins t1 r1 t3 (Arr a1 a) p s1))
        (values (App r2 w2) (ShApp k r1 r2 w w2 e s2) (RdApp h t3 r2 w2 a1 a f))))))

(def-adts $ (Suffix : ((Ty) c) ((Ty) a) -> Type)
  enum
  (many SufRefl : (erased (Ty) a) -> (Suffix a a))
  (many SufCod : (erased (Ty) c b d) (erased (Suffix c b) p) -> (Suffix c (Arr d b))))

(def-fns _ $ (erased suffix-cod : (erased (Ty) d c a) (subterm erased (Suffix (Arr d c) a) p) -> (erased (Suffix c a) q))
  (match erased p _
    ((SufRefl _) (SufCod c c d (SufRefl c)))
    ((SufCod _ b e p1) (SufCod c b e (suffix-cod d c b p1)))))

(def-fns _ $ (erased suffix-dom : (erased (Ty) d c a) (subterm erased (Suffix (Arr d c) a) p) -> (erased (Subterm (Ty) d (Ty) a) q))
  (match erased p _
    ((SufRefl _) (prove-subterm d (Arr d c)))
    ((SufCod _ b e p1) (subterm-trans (suffix-dom d c b p1) (prove-subterm b (Arr e b))))))

(def-adts $ (NeRes : ((List (Ty)) g) ((Term) n) ((Ty) c) ((Ty) a) -> Type)
  enum
  (many NRNe : (erased (List (Ty)) g) (erased (Term) n) (erased (Ty) c a) (erased (SNe g n c) p) -> (NeRes g n c a))
  (many NRHead : (erased (List (Ty)) g) (erased (Term) n) (erased (Ty) c a) (erased (SN g n c) p) (erased (Suffix c a) q) -> (NeRes g n c a)))

(def-fns _
  ((erased sub-sn : (subterm erased (Ty) a) (erased (List (Ty)) g h) (erased (Term) r) (erased (Ty) c) (subterm erased (SN h r c) d)
      (erased (Nat) x) (erased (Ins x a g h) ins) (erased (Term) s) (erased (SN g s a) ds) (erased (Term) r2) (erased (Sub x s r r2) sb)
      -> (erased (SN g r2 c) e))
    (match erased d _
      ((SNNe _ _ _ p)
        (match erased (sub-ne a g h r c p x ins s ds r2 sb) _
          ((NRNe _ _ _ _ e) (SNNe g r2 c e))
          ((NRHead _ _ _ _ e _) e)))
      ((SNLam _ t1 a1 c1 p)
        (let-match erased sb (SubLam _ _ s1 _ t2 sh sb1))
        (SNLam g t2 a1 c1 (sub-sn a (Cons _ a1 g) (Cons _ a1 h) t1 c1 p (Succ x) (InsS x a a1 g h ins) s1
          (wk-sn g (Cons _ a1 g) (Zero) a1 (InsZ a1 g) s s1 a ds sh) t2 sb1)))
      ((SNExp _ _ r1 _ p q)
        (let ((erased r3) (erased f) (erased p2)) (sub-red a g h r r1 c p x ins s ds r2 sb))
        (SNExp g r2 r3 c p2 (sub-sn a g h r1 c q x ins s ds r3 f)))))
  ((erased sub-ne : (subterm erased (Ty) a) (erased (List (Ty)) g h) (erased (Term) n) (erased (Ty) c) (subterm erased (SNe h n c) d)
      (erased (Nat) x) (erased (Ins x a g h) ins) (erased (Term) s) (erased (SN g s a) ds) (erased (Term) n2) (erased (Sub x s n n2) sb)
      -> (erased (NeRes g n2 c a) e))
    (match erased d _
      ((NeVar _ j _ p)
        (match erased sb _
          ((SubHit _ _)
            (let-match erased (nth-det h x c a p (ins-hit x a g h ins)) (Refl _ _))
            (NRHead g s a a ds (SufRefl a)))
          ((SubMiss _ _ i _ sk) (NRNe g (Var i) c a (NeVar g i c (ins-back x a g h ins i j sk c p))))))
      ((NeApp _ m w b _ p q)
        (let-match erased sb (SubApp _ _ _ m2 _ w2 sm sw))
        (let ((erased ew)) (sub-sn a g h w b q x ins s ds w2 sw))
        (match erased (sub-ne a g h m (Arr b c) p x ins s ds m2 sm) _
          ((NRNe _ _ _ _ e) (NRNe g n2 c a (NeApp g m2 w2 b c e ew)))
          ((NRHead _ _ _ _ e suf)
            (NRHead g n2 c a (app-sn (subterm (suffix-dom b c a suf)) b g m2 c e w2 ew) (suffix-cod b c a suf)))))))
  ((erased sub-red : (subterm erased (Ty) a) (erased (List (Ty)) g h) (erased (Term) r r1) (erased (Ty) c) (subterm erased (SNRed h r r1 c) d)
      (erased (Nat) x) (erased (Ins x a g h) ins) (erased (Term) s) (erased (SN g s a) ds) (erased (Term) r2) (erased (Sub x s r r2) sb)
      -> (erased (Term) r3) (erased (Sub x s r1 r3) f) (erased (SNRed g r2 r3 c) q))
    (match erased d _
      ((RdBeta _ b u _ b1 _ p q)
        (let-match erased sb (SubApp _ _ _ l2 _ u2 sl su))
        (let-match erased sl (SubLam _ _ s1 _ b2 sh sb1))
        (let ((erased r3) (erased f) (erased g1)) (sub-sub (Zero) x u b r1 s s1 b2 u2 q sh sb1 su (LtZ x)))
        (values r3 f (RdBeta g b2 u2 r3 b1 c (sub-sn a g h u b1 p x ins s ds u2 su) g1)))
      ((RdApp _ t0 t1 w b1 _ p)
        (let-match erased sb (SubApp _ _ _ t2 _ w2 st sw))
        (let ((erased t3) (erased f) (erased q2)) (sub-red a g h t0 t1 (Arr b1 c) p x ins s ds t2 st))
        (values (App t3 w2) (SubApp x s t1 t3 w w2 f sw) (RdApp g t2 t3 w2 b1 c q2)))))
  ((erased app-sn : (subterm erased (Ty) a) (erased (List (Ty)) g) (erased (Term) r) (erased (Ty) c) (subterm erased (SN g r (Arr a c)) d)
      (erased (Term) s) (erased (SN g s a) ds) -> (erased (SN g (App r s) c) e))
    (match erased d _
      ((SNNe _ _ _ p) (SNNe g (App r s) c (NeApp g r s a c p ds)))
      ((SNLam _ b _ _ p)
        (let ((erased r2) (erased sb)) (sub-ex (Zero) s b))
        (SNExp g (App r s) r2 c (RdBeta g b s r2 a c ds sb) (sub-sn a g (Cons _ a g) b c p (Zero) (InsZ a g) s ds r2 sb)))
      ((SNExp _ _ r1 _ p q)
        (SNExp g (App r s) (App r1 s) c (RdApp g r r1 s a c p) (app-sn a g r1 c q s ds))))))

(def-fns _ $ (erased typed-sn : (erased (List (Ty)) g) (erased (Term) t) (erased (Ty) a) (subterm erased (Typed g t a) h) -> (erased (SN g t a) d))
  (match erased h _
    ((TyVar _ i _ p) (SNNe g t a (NeVar g i a p)))
    ((TyLam _ b a1 c p) (SNLam g b a1 c (typed-sn (Cons _ a1 g) b c p)))
    ((TyApp _ f x a1 _ p q) (app-sn a1 g f a (typed-sn g f (Arr a1 a) p) x (typed-sn g x a1 q)))))
