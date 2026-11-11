(def-adts $ (Steps : ((Term) t) ((Term) u) -> Type)
  enum
  (many SRefl : (erased (Term) t) -> (Steps t t))
  (many SStep : (erased (Term) t u v) (erased (Step t u) p) (erased (Steps u v) q) -> (Steps t v)))

(def-fns _ $ (erased sn-steps : (erased (Term) t u) (erased (Sn t) d) (subterm erased (Steps t u) s) -> (erased (Sn u) e))
  (match erased s _
    ((SRefl _) d)
    ((SStep _ m _ p q) (let ((erased dm) (erased _)) (sn-step t m d p)) (sn-steps m u dm q))))

(def-fns _ $ (erased steps-plug : (erased (Frame) fr) (erased (Term) t u tt uu) (subterm erased (Steps t u) s) (erased (Plug fr t tt) p) (erased (Plug fr u uu) q)
    -> (erased (Steps tt uu) r))
  (match erased s _
    ((SRefl _) (let-match erased (plug-det fr t tt uu p q) (Refl _ _)) (SRefl tt))
    ((SStep _ m _ s1 s2)
      (let ((erased mm) (erased pm)) (plug-ex fr m))
      (SStep tt mm uu (step-plug fr t m tt mm s1 p pm) (steps-plug fr m u mm uu s2 pm q)))))

(def-fns _ $ (erased steps-trans : (erased (Term) a b c) (subterm erased (Steps a b) p) (erased (Steps b c) q) -> (erased (Steps a c) r))
  (match erased p _
    ((SRefl _) q)
    ((SStep _ m _ s p1) (SStep a m c s (steps-trans m b c p1 q)))))

(def-adts $ (Neutral : ((Term) t) -> Type)
  enum
  (many NeV : (erased (Nat) i) -> (Neutral (Var i)))
  (many NeA : (erased (Term) n u) (erased (Neutral n) p) -> (Neutral (App n u))))

(def-fns _ $ (erased ne-step : (erased (Term) n m) (subterm erased (Neutral n) p) (erased (Step n m) s) -> (erased (Neutral m) q))
  (match erased p _
    (absurd (NeV _) s)
    ((NeA n0 u p0)
      (match erased s _
        (absurd (StBeta _ _ _ _) p0)
        ((StAppL _ n1 _ s1) (NeA n1 u (ne-step n0 n1 p0 s1)))
        ((StAppR _ _ u1 _) (NeA n0 u1 p0))))))

(def-fns _ $ (erased shift-step : (erased (Nat) k) (erased (Term) t t1 u) (erased (Shift k t t1) sh) (subterm erased (Step t u) s)
    -> (erased (Term) u1) (erased (Shift k u u1) e) (erased (Step t1 u1) f))
  (match erased s _
    ((StBeta b a _ p)
      (let-match erased sh (ShApp _ _ _ _ a1 s1 s2))
      (let-match erased s1 (ShLam _ _ b1 s3))
      (let ((erased u1) (erased e) (erased f)) (shift-sub (Zero) k a b u b1 a1 p s3 s2 (LtZ k)))
      (values u1 e (StBeta b1 a1 u1 f)))
    ((StLam b c p)
      (let-match erased sh (ShLam _ _ b1 s1))
      (let ((erased c1) (erased e) (erased f)) (shift-step (Succ k) b b1 c s1 p))
      (values (Lam c1) (ShLam k c c1 e) (StLam b1 c1 f)))
    ((StAppL f g a p)
      (let-match erased sh (ShApp _ _ f1 _ a1 s1 s2))
      (let ((erased g1) (erased e) (erased q)) (shift-step k f f1 g s1 p))
      (values (App g1 a1) (ShApp k g g1 a a1 e s2) (StAppL f1 g1 a1 q)))
    ((StAppR f a b p)
      (let-match erased sh (ShApp _ _ f1 _ a1 s1 s2))
      (let ((erased b1) (erased e) (erased q)) (shift-step k a a1 b s2 p))
      (values (App f1 b1) (ShApp k f f1 b b1 s1 e) (StAppR f1 a1 b1 q)))))

(def-fns _ $ (erased sub-step-l : (erased (Nat) k) (erased (Term) u b r c) (erased (Sub k u b r) sb) (subterm erased (Step b c) s)
    -> (erased (Term) r1) (erased (Sub k u c r1) e) (erased (Step r r1) f))
  (match erased s _
    ((StBeta b0 a _ p)
      (let-match erased sb (SubApp _ _ _ _ _ a1 s1 s2))
      (let-match erased s1 (SubLam _ _ u1 _ b1 sh s3))
      (let ((erased r1) (erased e) (erased f)) (sub-sub (Zero) k a b0 c u u1 b1 a1 p sh s3 s2 (LtZ k)))
      (values r1 e (StBeta b1 a1 r1 f)))
    ((StLam b0 c0 p)
      (let-match erased sb (SubLam _ _ u1 _ b1 sh s1))
      (let ((erased c1) (erased e) (erased f)) (sub-step-l (Succ k) u1 b0 b1 c0 s1 p))
      (values (Lam c1) (SubLam k u u1 c0 c1 sh e) (StLam b1 c1 f)))
    ((StAppL f g a p)
      (let-match erased sb (SubApp _ _ _ f1 _ a1 s1 s2))
      (let ((erased g1) (erased e) (erased q)) (sub-step-l k u f f1 g s1 p))
      (values (App g1 a1) (SubApp k u g g1 a a1 e s2) (StAppL f1 g1 a1 q)))
    ((StAppR f a a2 p)
      (let-match erased sb (SubApp _ _ _ f1 _ a1 s1 s2))
      (let ((erased b1) (erased e) (erased q)) (sub-step-l k u a a1 a2 s2 p))
      (values (App f1 b1) (SubApp k u f f1 a2 b1 s1 e) (StAppR f1 a1 b1 q)))))

(def-fns _ $ (erased sub-step-r : (erased (Nat) k) (erased (Term) u b r v) (subterm erased (Sub k u b r) sb) (erased (Step u v) s)
    -> (erased (Term) r1) (erased (Sub k v b r1) e) (erased (Steps r r1) f))
  (match erased sb _
    ((SubHit _ _) (values v (SubHit k v) (SStep u v v s (SRefl v))))
    ((SubMiss _ _ i j p) (values r (SubMiss k v i j p) (SRefl r)))
    ((SubLam _ _ u1 c c1 sh s1)
      (let ((erased v1) (erased e) (erased f)) (shift-step (Zero) u u1 v sh s))
      (let ((erased c2) (erased g) (erased ss)) (sub-step-r (Succ k) u1 c c1 v1 s1 f))
      (values (Lam c2) (SubLam k v v1 c c2 e g) (steps-plug (FLam) c1 c2 r (Lam c2) ss (PLam c1) (PLam c2))))
    ((SubApp _ _ f g a h p q)
      (let ((erased g1) (erased e1) (erased ss1)) (sub-step-r k u f g v p s))
      (let ((erased h1) (erased e2) (erased ss2)) (sub-step-r k u a h v q s))
      (values (App g1 h1) (SubApp k v f g1 a h1 e1 e2)
        (steps-trans r (App g1 h) (App g1 h1) (steps-plug (FL h) g g1 r (App g1 h) ss1 (PL h g) (PL h g1))
          (steps-plug (FR g1) h h1 (App g1 h) (App g1 h1) ss2 (PR g1 h) (PR g1 h1)))))))

(def-adts $ (HeadRed : ((Term) t) ((Term) r) ((Term) u) -> Type)
  enum
  (many HRBeta : (erased (Term) b u r) (erased (Sub (Zero) u b r) p) -> (HeadRed (App (Lam b) u) r u))
  (many HRApp : (erased (Term) t r w u) (erased (HeadRed t r u) p) -> (HeadRed (App t w) (App r w) u)))

(def-adts $ (HSRes : ((Term) t) ((Term) r) ((Term) u) -> Type)
  enum
  (many HSHead : (erased (Term) t u) -> (HSRes t t u))
  (many HSIn : (erased (Term) t r u r1) (erased (HeadRed t r1 u) p) (erased (Step r r1) q) -> (HSRes t r u))
  (many HSArg : (erased (Term) t r u u1 r1) (erased (Step u u1) s) (erased (HeadRed t r1 u1) p) (erased (Steps r r1) q) -> (HSRes t r u)))

(def-fns _ $ (erased head-step : (erased (Term) t r u t1) (subterm erased (HeadRed t r u) hr) (erased (Step t t1) s) -> (erased (HSRes t1 r u) e))
  (match erased hr _
    ((HRBeta b _ _ p)
      (match erased s _
        ((StBeta _ _ _ q) (let-match erased (sub-det (Zero) u b r t1 p q) (Refl _ _)) (HSHead t1 u))
        ((StAppL _ g _ s1)
          (let-match erased s1 (StLam _ b1 s2))
          (let ((erased r1) (erased f) (erased s3)) (sub-step-l (Zero) u b r b1 p s2))
          (HSIn t1 r u r1 (HRBeta b1 u r1 f) s3))
        ((StAppR _ _ u1 s1)
          (let ((erased r1) (erased f) (erased ss)) (sub-step-r (Zero) u b r u1 p s1))
          (HSArg t1 r u u1 r1 s1 (HRBeta b u1 r1 f) ss))))
    ((HRApp t0 r0 w _ p)
      (match erased s _
        (absurd (StBeta _ _ _ _) p)
        ((StAppL _ g _ s1)
          (match erased (head-step t0 r0 u g p s1) _
            ((HSHead _ _) (HSHead t1 u))
            ((HSIn _ _ _ r1 p1 q1) (HSIn t1 r u (App r1 w) (HRApp g r1 w u p1) (StAppL r0 r1 w q1)))
            ((HSArg _ _ _ u1 r1 s2 p1 q1)
              (HSArg t1 r u u1 (App r1 w) s2 (HRApp g r1 w u1 p1) (steps-plug (FL w) r0 r1 r (App r1 w) q1 (PL w r0) (PL w r1))))))
        ((StAppR _ _ w1 s1) (HSIn t1 r u (App r0 w1) (HRApp t0 r0 w1 u p) (StAppR r0 w w1 s1)))))))
