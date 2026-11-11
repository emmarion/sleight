(def-fns _ $ (erased add-cancel-l : (erased (Nat) a b c x) (subterm erased (Add a b x) p) (erased (Add a c x) q) -> (erased (Eq (Nat) b c) e))
  (let-match erased p (AddSucc a1 _ x1 p1) ((AddZero _) (let-match erased q (AddZero _)) (Refl _ b)))
  (let-match erased q (AddSucc _ _ _ q1))
  (add-cancel-l a1 b c x1 p1 q1))

(def-fns _ $ (erased add4-swap : (erased (Nat) a b c d ab cd s ac bd)
    (erased (Add a b ab) p) (erased (Add c d cd) q) (erased (Add ab cd s) r) (erased (Add a c ac) u) (erased (Add b d bd) v) ->
    (erased (Add ac bd s) w))
  (let ((erased bcd) (erased r1) (erased r2)) (add-reassoc a b cd ab s p r))
  (let ((erased bc) (erased r3) (erased r4)) (add-assoc-back b c d cd bcd r1 q))
  (let ((erased bd1) (erased r5) (erased r6)) (add-reassoc c b d bc bcd (add-comm b c bc r3) r4))
  (let-match erased (add-fn b d bd bd1 v r5) (Refl _ _))
  (let ((erased ac1) (erased r7) (erased r8)) (add-assoc-back a c bd bcd s r2 r6))
  (let-match erased (add-fn a c ac ac1 u r7) (Refl _ _))
  r8)

(def-adts $ (DiffEq : ((Nat) a) ((Nat) b) ((Nat) c) ((Nat) d) -> Type)
  enum
  (many MkDiffEq : (erased (Nat) a b c d s) (erased (Add a d s) l) (erased (Add c b s) r) -> (DiffEq a b c d)))

(def-fns _ $ (erased diff-refl : (erased (Nat) a b) -> (erased (DiffEq a b a b) e))
  (let ((erased s) (erased p)) (add a b))
  (MkDiffEq a b a b s p p))

(def-fns _ $ (erased diff-sym : (erased (Nat) a b c d) (erased (DiffEq a b c d) e) -> (erased (DiffEq c d a b) f))
  (let-match erased e (MkDiffEq _ _ _ _ s l r))
  (MkDiffEq c d a b s r l))

(def-fns _ $ (erased diff-trans : (erased (Nat) a b c d e f) (erased (DiffEq a b c d) g) (erased (DiffEq c d e f) h) -> (erased (DiffEq a b e f) k))
  (let-match erased g (MkDiffEq _ _ _ _ s l1 r1))
  (let-match erased h (MkDiffEq _ _ _ _ t l2 r2))
  (let ((erased u) (erased pu)) (add a f))
  (let ((erased v) (erased pv)) (add e b))
  (let ((erased w) (erased pw)) (add d c))
  (let ((erased x) (erased px)) (add u w))
  (let ((erased y) (erased py)) (add v w))
  (let ((erased z) (erased pz)) (add s t))
  (let-match erased (add-fn s t x z (add4-swap a f d c u w x s t pu pw px l1 (add-comm c f t l2)) pz) (Refl _ _))
  (let-match erased (add-fn t s y z (add4-swap e b d c v w y t s pv pw py r2 (add-comm c b s r1)) (add-comm s t z pz)) (Refl _ _))
  (let-match erased (add-cancel-l w u v x (add-comm u w x px) (add-comm v w x py)) (Refl _ _))
  (MkDiffEq a b e f u pu pv))

(def-fns _ $ (erased diff-add : (erased (Nat) a b c d e f g h ae bf cg dh) (erased (DiffEq a b c d) p) (erased (DiffEq e f g h) q)
    (erased (Add a e ae) h1) (erased (Add b f bf) h2) (erased (Add c g cg) h3) (erased (Add d h dh) h4) -> (erased (DiffEq ae bf cg dh) r))
  (let-match erased p (MkDiffEq _ _ _ _ s l1 r1))
  (let-match erased q (MkDiffEq _ _ _ _ t l2 r2))
  (let ((erased x) (erased px)) (add s t))
  (MkDiffEq ae bf cg dh x (add4-swap a d e h s t x ae dh l1 l2 px h1 h4) (add4-swap c b g f s t x cg bf r1 r2 px h3 h2)))

(def-fns _ $ (erased diff-mul : (erased (Nat) a b c d e f ae bf af be ce df cf de l1 r1 l2 r2) (erased (DiffEq a b c d) p)
    (erased (Mul a e ae) m1) (erased (Mul b f bf) m2) (erased (Mul a f af) m3) (erased (Mul b e be) m4)
    (erased (Mul c e ce) m5) (erased (Mul d f df) m6) (erased (Mul c f cf) m7) (erased (Mul d e de) m8)
    (erased (Add ae bf l1) h1) (erased (Add af be r1) h2) (erased (Add ce df l2) h3) (erased (Add cf de r2) h4) -> (erased (DiffEq l1 r1 l2 r2) r))
  (let-match erased p (MkDiffEq _ _ _ _ s ls rs))
  (let ((erased se) (erased pse)) (mul s e))
  (let ((erased sf) (erased psf)) (mul s f))
  (let ((erased x) (erased px)) (add se sf))
  (let ((erased ha) (erased hb)) (values (mul-distr a d s e ae de se ls m1 m8 pse) (mul-distr b c s f bf cf sf (add-comm c b s rs) m2 m7 psf)))
  (let ((erased hc) (erased hd)) (values (mul-distr c b s e ce be se rs m5 m4 pse) (mul-distr d a s f df af sf (add-comm a d s ls) m6 m3 psf)))
  (MkDiffEq l1 r1 l2 r2 x (add4-swap ae de bf cf se sf x l1 r2 ha hb px h1 (add-comm cf de r2 h4))
    (add4-swap ce be df af se sf x l2 r1 hc hd px h3 (add-comm af be r1 h2))))

(def-fns _ $ (erased zview-fn : (erased (Z) a) (erased (Nat) p q p2 q2) (erased (ZView a p q) v) (erased (ZView a p2 q2) w) ->
    (erased (Eq (Nat) p p2) e) (erased (Eq (Nat) q q2) f))
  (match erased v _
    ((ZView0) (let-match erased w (ZView0)) (values (Refl _ p) (Refl _ q)))
    ((ZViewPos _) (let-match erased w (ZViewPos _)) (values (Refl _ p) (Refl _ q)))
    ((ZViewNeg _) (let-match erased w (ZViewNeg _)) (values (Refl _ p) (Refl _ q)))))

(def-fns _ $ (erased zview-diff : (erased (Z) a b) (erased (Nat) pa qa pb qb) (erased (ZView a pa qa) v) (erased (ZView b pb qb) w)
    (erased (DiffEq pa qa pb qb) d) -> (erased (Eq (Z) a b) e))
  (let-match erased d (MkDiffEq _ _ _ _ s l r))
  (match erased v _
    ((ZView0)
      (let-match erased l (AddZero _))
      (match erased w _ ((ZView0) (Refl _ a)) ((ZViewPos _) (match erased r _)) ((ZViewNeg _) (match erased r _))))
    ((ZViewPos j)
      (match erased w _
        ((ZView0) (let-match erased r (AddZero _)) (match erased l _))
        ((ZViewPos k)
          (let-match erased (add-fn _ _ _ _ l (add-zero-right _)) (Refl _ _))
          (let-match erased (add-fn _ _ _ _ r (add-zero-right _)) (Refl _ _))
          (Refl _ a))
        ((ZViewNeg _) (let-match erased r (AddZero _)) (match erased l _))))
    ((ZViewNeg j)
      (let-match erased l (AddZero _))
      (match erased w _
        ((ZView0) (match erased r _))
        ((ZViewPos _) (match erased r _))
        ((ZViewNeg k) (let-match erased r (AddZero _)) (Refl _ a))))))

(def-adts $ (ZOf : ((Z) z) ((Nat) x) ((Nat) y) -> Type)
  enum
  (many MkZOf : (erased (Z) z) (erased (Nat) x y p q) (erased (ZView z p q) v) (erased (DiffEq p q x y) d) -> (ZOf z x y)))

(def-fns _ $ (erased zof-view : (erased (Z) z) (erased (Nat) x y p q) (erased (ZOf z x y) o) (erased (ZView z p q) v) -> (erased (DiffEq p q x y) d))
  (let-match erased o (MkZOf _ _ _ p2 q2 w d))
  (let ((erased e1) (erased e2)) (zview-fn z p2 q2 p q w v))
  (let-match erased e1 (Refl _ _))
  (let-match erased e2 (Refl _ _))
  d)

(def-fns _ $ (erased zof-eq : (erased (Z) a b) (erased (Nat) x1 y1 x2 y2) (erased (ZOf a x1 y1) o1) (erased (ZOf b x2 y2) o2)
    (erased (DiffEq x1 y1 x2 y2) d) -> (erased (Eq (Z) a b) e))
  (let-match erased o1 (MkZOf _ _ _ pa qa va da))
  (let-match erased o2 (MkZOf _ _ _ pb qb vb db))
  (zview-diff a b pa qa pb qb va vb (diff-trans _ _ _ _ _ _ (diff-trans _ _ _ _ _ _ da d) (diff-sym _ _ _ _ db))))

(def-fns _ $ (erased zof-diff : (erased (Z) a) (erased (Nat) x1 y1 x2 y2) (erased (ZOf a x1 y1) o1) (erased (ZOf a x2 y2) o2) ->
    (erased (DiffEq x1 y1 x2 y2) d))
  (let-match erased o1 (MkZOf _ _ _ p q v d1))
  (diff-trans _ _ _ _ _ _ (diff-sym _ _ _ _ d1) (zof-view a x2 y2 p q o2 v)))

(def-fns _ $ (erased zof-rep : (erased (Z) a) (erased (Nat) x1 y1 x2 y2) (erased (ZOf a x1 y1) o) (erased (DiffEq x1 y1 x2 y2) d) ->
    (erased (ZOf a x2 y2) o2))
  (let-match erased o (MkZOf _ _ _ p q v d1))
  (MkZOf a x2 y2 p q v (diff-trans _ _ _ _ _ _ d1 d)))

(def-fns _ $ (erased zview-of : (erased (Z) a) (erased (Nat) p q) (erased (ZView a p q) v) -> (erased (ZOf a p q) o))
  (MkZOf a p q p q v (diff-refl p q)))

(def-fns _ $ (many zview : (many (Z) z) -> (many (Nat) p q) (erased (ZView z p q) v))
  (match many z _
    ((Z0) (values (Zero) (Zero) (ZView0)))
    ((Zpos k) (values (Succ k) (Zero) (ZViewPos k)))
    ((Zneg k) (values (Zero) (Succ k) (ZViewNeg k)))))

(def-fns _ $ (many zof-nat : (many (Nat) x y) -> (many (Z) z) (erased (ZOf z x y) o))
  (match many (nat-cmp x y) _
    ((CLt _ _ _ _ lt)
      (let ((many k) (erased h)) (sub y (Succ x) (LtS x y lt)))
      (let-match erased h (AddSucc _ _ y1 h1))
      (values (Zneg k) (MkZOf _ x y _ _ (ZViewNeg k) (MkDiffEq _ _ x y y (AddZero y) (add-succ-right x k y1 h1)))))
    ((CEq _ _ _) (values (Z0) (MkZOf _ x y _ _ (ZView0) (MkDiffEq _ _ x y x (AddZero x) (add-zero-right x)))))
    ((CGt _ _ _ _ gt)
      (let ((many k) (erased h)) (sub x (Succ y) (LtS y x gt)))
      (let-match erased h (AddSucc _ _ x1 h1))
      (values (Zpos k) (MkZOf _ x y _ _ (ZViewPos k) (MkDiffEq _ _ x y x (AddSucc k y x1 (add-comm y k x1 h1)) (add-zero-right x)))))))

(def-fns _ $ (erased zadd-intro : (erased (Z) a b c) (erased (Nat) pa qa pb qb l r) (erased (ZView a pa qa) va) (erased (ZView b pb qb) vb)
    (erased (Add pa pb l) hl) (erased (Add qa qb r) hr) (erased (ZOf c l r) o) -> (erased (ZAdd a b c) h))
  (let-match erased o (MkZOf _ _ _ pc qc vc d))
  (let-match erased d (MkDiffEq _ _ _ _ t h1 h2))
  (MkZAdd a b c pa qa pb qb pc qc l r t va vb vc hl h2 hr (add-comm pc r t h1)))

(def-fns _ $ (many zadd : (many (Z) a b) -> (many (Z) c) (erased (ZAdd a b c) h))
  (let ((many pa) (many qa) (erased va)) (zview a))
  (let ((many pb) (many qb) (erased vb)) (zview b))
  (let ((many l) (erased hl)) (add pa pb))
  (let ((many r) (erased hr)) (add qa qb))
  (let ((many c) (erased o)) (zof-nat l r))
  (values c (zadd-intro a b c pa qa pb qb l r va vb hl hr o)))

(def-fns _ $ (erased zadd-rep : (erased (Z) a b c) (erased (Nat) x1 y1 x2 y2 x y) (erased (ZAdd a b c) h) (erased (ZOf a x1 y1) o1) (erased (ZOf b x2 y2) o2)
    (erased (Add x1 x2 x) h1) (erased (Add y1 y2 y) h2) -> (erased (ZOf c x y) o))
  (let-match erased h (MkZAdd _ _ _ pa qa pb qb pc qc l r t va vb vc hl hlt hr hrt))
  (MkZOf c x y pc qc vc (diff-trans _ _ _ _ _ _ (MkDiffEq pc qc l r t (add-comm r pc t hrt) hlt)
    (diff-add _ _ _ _ _ _ _ _ _ _ _ _ (zof-view a x1 y1 pa qa o1 va) (zof-view b x2 y2 pb qb o2 vb) hl hr h1 h2))))

(def-fns _ $ (erased zmul-intro : (erased (Z) a b c) (erased (Nat) pa qa pb qb m1 m2 m3 m4 l r) (erased (ZView a pa qa) va) (erased (ZView b pb qb) vb)
    (erased (Mul pa pb m1) h1) (erased (Mul qa qb m2) h2) (erased (Mul pa qb m3) h3) (erased (Mul qa pb m4) h4)
    (erased (Add m1 m2 l) hl) (erased (Add m3 m4 r) hr) (erased (ZOf c l r) o) -> (erased (ZMul a b c) h))
  (let-match erased o (MkZOf _ _ _ pc qc vc d))
  (let-match erased d (MkDiffEq _ _ _ _ t k1 k2))
  (MkZMul a b c pa qa pb qb pc qc m1 m2 m3 m4 l r t va vb vc h1 h2 h3 h4 hl k2 hr (add-comm pc r t k1)))

(def-fns _ $ (many zmul : (many (Z) a b) -> (many (Z) c) (erased (ZMul a b c) h))
  (let ((many pa) (many qa) (erased va)) (zview a))
  (let ((many pb) (many qb) (erased vb)) (zview b))
  (let ((many m1) (erased h1)) (mul pa pb))
  (let ((many m2) (erased h2)) (mul qa qb))
  (let ((many m3) (erased h3)) (mul pa qb))
  (let ((many m4) (erased h4)) (mul qa pb))
  (let ((many l) (erased hl)) (add m1 m2))
  (let ((many r) (erased hr)) (add m3 m4))
  (let ((many c) (erased o)) (zof-nat l r))
  (values c (zmul-intro a b c pa qa pb qb m1 m2 m3 m4 l r va vb h1 h2 h3 h4 hl hr o)))

(def-fns _ $ (erased zmul-rep : (erased (Z) a b c) (erased (Nat) x1 y1 x2 y2 n1 n2 n3 n4 x y) (erased (ZMul a b c) h)
    (erased (ZOf a x1 y1) o1) (erased (ZOf b x2 y2) o2)
    (erased (Mul x1 x2 n1) k1) (erased (Mul y1 y2 n2) k2) (erased (Mul x1 y2 n3) k3) (erased (Mul y1 x2 n4) k4)
    (erased (Add n1 n2 x) hx) (erased (Add n3 n4 y) hy) -> (erased (ZOf c x y) o))
  (let-match erased h (MkZMul _ _ _ pa qa pb qb pc qc m1 m2 m3 m4 l r t va vb vc h1 h2 h3 h4 hl hlt hr hrt))
  (let ((erased u1) (erased g1)) (mul x1 pb))
  (let ((erased u2) (erased g2)) (mul y1 qb))
  (let ((erased u3) (erased g3)) (mul x1 qb))
  (let ((erased u4) (erased g4)) (mul y1 pb))
  (let ((erased l2) (erased f1)) (add u1 u2))
  (let ((erased r2) (erased f2)) (add u3 u4))
  (let ((erased d1)) (diff-mul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (zof-view a x1 y1 pa qa o1 va) h1 h2 h3 h4 g1 g2 g3 g4 hl hr f1 f2))
  (let ((erased d2)) (diff-mul _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (zof-view b x2 y2 pb qb o2 vb)
    (mul-comm _ _ _ g1) (mul-comm _ _ _ g2) (mul-comm _ _ _ g4) (mul-comm _ _ _ g3)
    (mul-comm _ _ _ k1) (mul-comm _ _ _ k2) (mul-comm _ _ _ k4) (mul-comm _ _ _ k3)
    f1 (add-comm _ _ _ f2) hx (add-comm _ _ _ hy)))
  (MkZOf c x y pc qc vc (diff-trans _ _ _ _ _ _ (MkDiffEq pc qc l r t (add-comm r pc t hrt) hlt) (diff-trans _ _ _ _ _ _ d1 d2))))

(def-fns _ $ (erased zadd-fn : (erased (Z) a b c d) (erased (ZAdd a b c) h) (erased (ZAdd a b d) k) -> (erased (Eq (Z) c d) e))
  (let-match erased h (MkZAdd _ _ _ pa qa pb qb _ _ l r _ va vb _ hl _ hr _))
  (let ((erased oa) (erased ob)) (values (zview-of a pa qa va) (zview-of b pb qb vb)))
  (zof-eq c d l r l r (zadd-rep a b c pa qa pb qb l r h oa ob hl hr) (zadd-rep a b d pa qa pb qb l r k oa ob hl hr) (diff-refl l r)))

(def-fns _ $ (erased zmul-fn : (erased (Z) a b c d) (erased (ZMul a b c) h) (erased (ZMul a b d) k) -> (erased (Eq (Z) c d) e))
  (let-match erased h (MkZMul _ _ _ pa qa pb qb _ _ m1 m2 m3 m4 l r _ va vb _ h1 h2 h3 h4 hl _ hr _))
  (let ((erased oa) (erased ob)) (values (zview-of a pa qa va) (zview-of b pb qb vb)))
  (zof-eq c d l r l r (zmul-rep a b c pa qa pb qb m1 m2 m3 m4 l r h oa ob h1 h2 h3 h4 hl hr)
    (zmul-rep a b d pa qa pb qb m1 m2 m3 m4 l r k oa ob h1 h2 h3 h4 hl hr) (diff-refl l r)))

(def-fns _ $ (many zopp : (many (Z) a) -> (many (Z) b) (erased (ZOpp a b) h))
  (match many a _
    ((Z0) (values (Z0) (ZOpp0)))
    ((Zpos k) (values (Zneg k) (ZOppPos k)))
    ((Zneg k) (values (Zpos k) (ZOppNeg k)))))

(def-fns _ $ (many zabs : (many (Z) a) -> (many (Z) b) (erased (ZAbs a b) h))
  (match many a _
    ((Z0) (values (Z0) (ZAbs0)))
    ((Zpos k) (values (Zpos k) (ZAbsPos k)))
    ((Zneg k) (values (Zpos k) (ZAbsNeg k)))))

(def-fns _ $ (erased zopp-fn : (erased (Z) a b c) (erased (ZOpp a b) h) (erased (ZOpp a c) k) -> (erased (Eq (Z) b c) e))
  (match erased h _
    ((ZOpp0) (let-match erased k (ZOpp0)) (Refl _ b))
    ((ZOppPos _) (let-match erased k (ZOppPos _)) (Refl _ b))
    ((ZOppNeg _) (let-match erased k (ZOppNeg _)) (Refl _ b))))

(def-fns _ $ (erased zabs-fn : (erased (Z) a b c) (erased (ZAbs a b) h) (erased (ZAbs a c) k) -> (erased (Eq (Z) b c) e))
  (match erased h _
    ((ZAbs0) (let-match erased k (ZAbs0)) (Refl _ b))
    ((ZAbsPos _) (let-match erased k (ZAbsPos _)) (Refl _ b))
    ((ZAbsNeg _) (let-match erased k (ZAbsNeg _)) (Refl _ b))))

(def-fns _ $ (erased zopp-rep : (erased (Z) a b) (erased (Nat) x y) (erased (ZOpp a b) h) (erased (ZOf a x y) o) -> (erased (ZOf b y x) o2))
  (let-match erased o (MkZOf _ _ _ p q v d))
  (let-match erased d (MkDiffEq _ _ _ _ s l r))
  (let ((erased d2)) (MkDiffEq q p y x s (add-comm _ _ _ r) (add-comm _ _ _ l)))
  (match erased h _
    ((ZOpp0) (let-match erased v (ZView0)) (MkZOf b y x _ _ (ZView0) d2))
    ((ZOppPos k) (let-match erased v (ZViewPos _)) (MkZOf b y x _ _ (ZViewNeg k) d2))
    ((ZOppNeg k) (let-match erased v (ZViewNeg _)) (MkZOf b y x _ _ (ZViewPos k) d2))))

(def-adts $ (ZExpr : -> Type)
  enum
  (many ZEVar : (many (Nat) i) -> (ZExpr))
  (many ZENum : (many (Nat) k) -> (ZExpr))
  (many ZEAdd : (many (ZExpr) a b) -> (ZExpr))
  (many ZEMul : (many (ZExpr) a b) -> (ZExpr))
  (many ZEOpp : (many (ZExpr) a) -> (ZExpr)))

(def-adts $ (ZEval : ((List (Z)) env) ((ZExpr) e) ((Z) z) -> Type)
  enum
  (many ZEvVar : (erased (List (Z)) env) (erased (Nat) i) (erased (Z) z) (erased (Nth (Z) env i z) p) -> (ZEval env (ZEVar i) z))
  (many ZEvNum : (erased (List (Z)) env) (erased (Nat) k) (erased (Z) z) (erased (ZView z k (Zero)) v) -> (ZEval env (ZENum k) z))
  (many ZEvAdd : (erased (List (Z)) env) (erased (ZExpr) a b) (erased (Z) x y z)
     (erased (ZEval env a x) ea) (erased (ZEval env b y) eb) (erased (ZAdd x y z) h) -> (ZEval env (ZEAdd a b) z))
  (many ZEvMul : (erased (List (Z)) env) (erased (ZExpr) a b) (erased (Z) x y z)
     (erased (ZEval env a x) ea) (erased (ZEval env b y) eb) (erased (ZMul x y z) h) -> (ZEval env (ZEMul a b) z))
  (many ZEvOpp : (erased (List (Z)) env) (erased (ZExpr) a) (erased (Z) x z) (erased (ZEval env a x) ea) (erased (ZOpp x z) h)
     -> (ZEval env (ZEOpp a) z)))

(def-adts $ (ZTr : ((ZExpr) e) ((Expr) p) ((Expr) n) -> Type)
  enum
  (many ZTrVar : (erased (Nat) i j) (erased (Double i j) d) -> (ZTr (ZEVar i) (EVar j) (EVar (Succ j))))
  (many ZTrNum : (erased (Nat) k) -> (ZTr (ZENum k) (ENum k) (ENum (Zero))))
  (many ZTrAdd : (erased (ZExpr) a b) (erased (Expr) pa na pb nb) (erased (ZTr a pa na) ta) (erased (ZTr b pb nb) tb)
     -> (ZTr (ZEAdd a b) (EAdd pa pb) (EAdd na nb)))
  (many ZTrMul : (erased (ZExpr) a b) (erased (Expr) pa na pb nb) (erased (ZTr a pa na) ta) (erased (ZTr b pb nb) tb)
     -> (ZTr (ZEMul a b) (EAdd (EMul pa pb) (EMul na nb)) (EAdd (EMul pa nb) (EMul na pb))))
  (many ZTrOpp : (erased (ZExpr) a) (erased (Expr) pa na) (erased (ZTr a pa na) ta) -> (ZTr (ZEOpp a) na pa)))

(def-fns _ $ (many ztr : (subterm many (ZExpr) e) -> (many (Expr) p n) (erased (ZTr e p n) t))
  (match many e _
    ((ZEVar i) (let ((many j) (erased d)) (double i)) (values (EVar j) (EVar (Succ j)) (ZTrVar i j d)))
    ((ZENum k) (values (ENum k) (ENum (Zero)) (ZTrNum k)))
    ((ZEAdd a b)
      (let ((many pa) (many na) (erased ta)) (notail $ ztr a))
      (let ((many pb) (many nb) (erased tb)) (notail $ ztr b))
      (values (EAdd pa pb) (EAdd na nb) (ZTrAdd a b pa na pb nb ta tb)))
    ((ZEMul a b)
      (let ((many pa) (many na) (erased ta)) (notail $ ztr a))
      (let ((many pb) (many nb) (erased tb)) (notail $ ztr b))
      (values (EAdd (EMul pa pb) (EMul na nb)) (EAdd (EMul pa nb) (EMul na pb)) (ZTrMul a b pa na pb nb ta tb)))
    ((ZEOpp a)
      (let ((many pa) (many na) (erased ta)) (notail $ ztr a))
      (values na pa (ZTrOpp a pa na ta)))))

(def-adts $ (ZEnv : ((List (Z)) env) ((List (Nat)) ns) -> Type)
  enum
  (many ZEnvNil : -> (ZEnv (Nil (Z)) (Nil (Nat))))
  (many ZEnvCons : (erased (Z) z) (erased (Nat) p q) (erased (List (Z)) zs) (erased (List (Nat)) ns) (erased (ZView z p q) v) (erased (ZEnv zs ns) r)
     -> (ZEnv (Cons (Z) z zs) (Cons (Nat) p $ Cons (Nat) q ns))))

(def-fns _ $ (erased zenv : (subterm erased (List (Z)) env) -> (erased (List (Nat)) ns) (erased (ZEnv env ns) r))
  (let-match erased env (Cons _ z zs) ((Nil _) (values (Nil (Nat)) (ZEnvNil))))
  (let ((erased p) (erased q) (erased v)) (zview z))
  (let ((erased ns) (erased r)) (zenv zs))
  (values (Cons (Nat) p $ Cons (Nat) q ns) (ZEnvCons z p q zs ns v r)))

(def-fns _ $ (erased zenv-nth : (erased (List (Z)) env) (erased (List (Nat)) ns) (erased (Nat) i j) (erased (Z) z)
    (erased (ZEnv env ns) r) (subterm erased (Nth (Z) env i z) n) (erased (Double i j) d) ->
    (erased (Nat) p q) (erased (ZView z p q) v) (erased (Nth (Nat) ns j p) np) (erased (Nth (Nat) ns (Succ j) q) nq))
  (match erased n _
    ((NthHere _ _ _) (let-match erased r (ZEnvCons _ p q zs ns1 v r1)) (let-match erased d (D0)) (values p q v (NthHere _ p _) (NthThere _ p _ _ q (NthHere _ q _))))
    ((NthThere _ _ _ i1 _ n1)
      (let-match erased r (ZEnvCons _ p q zs ns1 v r1))
      (let-match erased d (DS _ j1 d1))
      (let ((erased p1) (erased q1) (erased v1) (erased np) (erased nq)) (zenv-nth zs ns1 i1 j1 z r1 n1 d1))
      (values p1 q1 v1 (NthThere _ p _ _ p1 $ NthThere _ q _ _ p1 np) (NthThere _ p _ _ q1 $ NthThere _ q _ _ q1 nq)))))

(def-fns _ $ (erased zeval-sound : (erased (List (Z)) env) (erased (List (Nat)) ns) (erased (ZExpr) e) (erased (Expr) pe ne) (erased (Z) z)
    (erased (ZEnv env ns) r) (subterm erased (ZEval env e z) ev) (erased (ZTr e pe ne) t) ->
    (erased (Nat) x y) (erased (Eval ns pe x) vx) (erased (Eval ns ne y) vy) (erased (ZOf z x y) o))
  (match erased ev _
    ((ZEvVar _ i _ n)
      (let-match erased t (ZTrVar _ j d))
      (let ((erased p) (erased q) (erased v) (erased np) (erased nq)) (zenv-nth env ns i j z r n d))
      (values p q (EvVar ns j p np) (EvVar ns (Succ j) q nq) (zview-of z p q v)))
    ((ZEvNum _ k _ v)
      (let-match erased t (ZTrNum _))
      (values k (Zero) (EvNum ns k) (EvNum ns (Zero)) (zview-of z k (Zero) v)))
    ((ZEvAdd _ a b za zb _ ea eb h)
      (let-match erased t (ZTrAdd _ _ pa na pb nb ta tb))
      (let ((erased x1) (erased y1) (erased px1) (erased py1) (erased o1)) (zeval-sound env ns a pa na za r ea ta))
      (let ((erased x2) (erased y2) (erased px2) (erased py2) (erased o2)) (zeval-sound env ns b pb nb zb r eb tb))
      (let ((erased x) (erased hx)) (add x1 x2))
      (let ((erased y) (erased hy)) (add y1 y2))
      (values x y (EvAdd ns pa pb x1 x2 x px1 px2 hx) (EvAdd ns na nb y1 y2 y py1 py2 hy) (zadd-rep za zb z x1 y1 x2 y2 x y h o1 o2 hx hy)))
    ((ZEvMul _ a b za zb _ ea eb h)
      (let-match erased t (ZTrMul _ _ pa na pb nb ta tb))
      (let ((erased x1) (erased y1) (erased px1) (erased py1) (erased o1)) (zeval-sound env ns a pa na za r ea ta))
      (let ((erased x2) (erased y2) (erased px2) (erased py2) (erased o2)) (zeval-sound env ns b pb nb zb r eb tb))
      (let ((erased n1) (erased k1)) (mul x1 x2))
      (let ((erased n2) (erased k2)) (mul y1 y2))
      (let ((erased n3) (erased k3)) (mul x1 y2))
      (let ((erased n4) (erased k4)) (mul y1 x2))
      (let ((erased x) (erased hx)) (add n1 n2))
      (let ((erased y) (erased hy)) (add n3 n4))
      (values x y
        (EvAdd ns _ _ n1 n2 x (EvMul ns pa pb x1 x2 n1 px1 px2 k1) (EvMul ns na nb y1 y2 n2 py1 py2 k2) hx)
        (EvAdd ns _ _ n3 n4 y (EvMul ns pa nb x1 y2 n3 px1 py2 k3) (EvMul ns na pb y1 x2 n4 py1 px2 k4) hy)
        (zmul-rep za zb z x1 y1 x2 y2 n1 n2 n3 n4 x y h o1 o2 k1 k2 k3 k4 hx hy)))
    ((ZEvOpp _ a za _ ea h)
      (let-match erased t (ZTrOpp _ pa na ta))
      (let ((erased x1) (erased y1) (erased px1) (erased py1) (erased o1)) (zeval-sound env ns a pa na za r ea ta))
      (values y1 x1 py1 px1 (zopp-rep za z x1 y1 h o1)))))

(def-adts $ (ZRingEq : ((ZExpr) e1) ((ZExpr) e2) -> Type)
  enum
  (many MkZRingEq : (erased (ZExpr) e1 e2) (erased (Expr) p1 n1 p2 n2) (erased (ZTr e1 p1 n1) t1) (erased (ZTr e2 p2 n2) t2)
     (erased (RingEq (EAdd p1 n2) (EAdd p2 n1)) r) -> (ZRingEq e1 e2)))

(def-fns _ $ (many zring-check : (many (ZExpr) e1 e2) -> (many (Maybe (ZRingEq e1 e2)) r))
  (let ((many p1) (many n1) (erased t1)) (ztr e1))
  (let ((many p2) (many n2) (erased t2)) (ztr e2))
  (match many (ring-check (EAdd p1 n2) (EAdd p2 n1)) _
    ((Some _ r) (Some _ (MkZRingEq e1 e2 p1 n1 p2 n2 t1 t2 r)))
    ((None _) (None _))))

(def-fns _ $ (erased zring-sound : (erased (List (Z)) env) (erased (ZExpr) e1 e2) (erased (Z) z1 z2) (erased (ZRingEq e1 e2) h)
    (erased (ZEval env e1 z1) v1) (erased (ZEval env e2 z2) v2) -> (erased (Eq (Z) z1 z2) e))
  (let-match erased h (MkZRingEq _ _ p1 n1 p2 n2 t1 t2 r))
  (let ((erased ns) (erased en)) (zenv env))
  (let ((erased x1) (erased y1) (erased px1) (erased py1) (erased o1)) (zeval-sound env ns e1 p1 n1 z1 en v1 t1))
  (let ((erased x2) (erased y2) (erased px2) (erased py2) (erased o2)) (zeval-sound env ns e2 p2 n2 z2 en v2 t2))
  (let ((erased s1) (erased h1)) (add x1 y2))
  (let ((erased s2) (erased h2)) (add x2 y1))
  (let-match erased (ring-sound ns _ _ s1 s2 r (EvAdd ns p1 n2 x1 y2 s1 px1 py2 h1) (EvAdd ns p2 n1 x2 y1 s2 px2 py1 h2)) (Refl _ _))
  (zof-eq z1 z2 x1 y1 x2 y2 o1 o2 (MkDiffEq x1 y1 x2 y2 s1 h1 h2)))

(def-fns _ $ (many zindex-raw : (subterm many (Nat) k) -> (many (Raw) i) (many (Raw) n))
  (let-match many k (Succ k1)
    ((Zero) (let-match many (qq (Zero)) (Cons _ i _)) (let-match many (qq (NthHere _ _ _)) (Cons _ n _)) (values i n)))
  (let ((many i1) (many n1)) (notail $ zindex-raw k1))
  (let-match many (qq (Succ (~ i1))) (Cons _ i _))
  (let-match many (qq (NthThere _ _ _ _ _ (~ n1))) (Cons _ n _))
  (values i n))

(def-fns _ $ (many zindex-arg : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (Raw) i) (many (Raw) n))
  (let-match many args (Cons _ a _) ((Nil _) (let ((unique mw1) (many f)) (fail-raw mw here "expected a numeral")) (values mw1 f f)))
  (let ((unique mw1) (many k)) (arg-nat mw a))
  (let-match many k (Some _ k1) ((None _) (let ((unique mw2) (many f)) (fail-raw mw1 here "expected a numeral")) (values mw2 f f)))
  (let ((many i) (many n)) (zindex-raw k1))
  (values mw1 i n))

(def-macro (zvar args here mw)
  (let ((unique mw1) (many i) (many n)) (zindex-arg mw here args))
  (values mw1 (qq (ZEVar (~ i)))))

(def-macro (zev-var args here mw)
  (let ((unique mw1) (many i) (many n)) (zindex-arg mw here args))
  (values mw1 (qq (ZEvVar _ _ _ (~ n)))))

(def-macro (zev-add args)
  (qq (ZEvAdd _ _ _ _ _ _ (~@ args))))

(def-macro (zev-mul args)
  (qq (ZEvMul _ _ _ _ _ _ (~@ args))))

(def-macro (zev-opp args)
  (qq (ZEvOpp _ _ _ _ (~@ args))))

(def-fns _ $ (many znat : (many (Nat) n) -> (many (Z) z) (erased (ZView z n (Zero)) v))
  (match many n _ ((Zero) (values (Z0) (ZView0))) ((Succ k) (values (Zpos k) (ZViewPos k)))))

(def-adts $ (ZGap : ((Z) a) ((Z) b) ((Nat) n) -> Type)
  enum
  (many MkZGap : (erased (Z) a b d) (erased (Nat) n) (erased (ZView d n (Zero)) v) (erased (ZAdd a d b) h) -> (ZGap a b n)))

(def-fns _ $ (erased zgap-intro : (erased (Z) a b) (erased (Nat) pa qa pb qb l r n) (erased (ZView a pa qa) va) (erased (ZView b pb qb) vb)
    (erased (Add pa qb l) hl) (erased (Add pb qa r) hr) (erased (Add l n r) hn) -> (erased (ZGap a b n) g))
  (let ((erased d) (erased vd)) (znat n))
  (let ((erased s) (erased hs)) (add pa n))
  (let ((erased t) (erased h1) (erased h2)) (add-right-comm pa qb l n r hl hn))
  (let-match erased (add-fn pa n t s h1 hs) (Refl _ _))
  (MkZGap a b d n vd (zadd-intro a d b pa qa n (Zero) s qa va vd hs (add-zero-right qa) (MkZOf b s qa pb qb vb (MkDiffEq pb qb s qa r hr h2)))))

(def-fns _ $ (erased zgap-elim : (erased (Z) a b) (erased (Nat) pa qa pb qb l r n) (erased (ZView a pa qa) va) (erased (ZView b pb qb) vb)
    (erased (Add pa qb l) hl) (erased (Add pb qa r) hr) (erased (ZGap a b n) g) -> (erased (Add l n r) hn))
  (let-match erased g (MkZGap _ _ d _ vd h))
  (let ((erased s) (erased hs)) (add pa n))
  (let ((erased o)) (zadd-rep a d b pa qa n (Zero) s qa h (zview-of a pa qa va) (zview-of d n (Zero) vd) hs (add-zero-right qa)))
  (let-match erased (zof-view b s qa pb qb o vb) (MkDiffEq _ _ _ _ u h1 h2))
  (let-match erased (add-fn pb qa r u hr h1) (Refl _ _))
  (let ((erased t) (erased h3) (erased h4)) (add-right-comm pa n s qb r hs h2))
  (let-match erased (add-fn pa qb l t hl h3) (Refl _ _))
  h4)

(def-fns _ $ (erased zlt-gap : (erased (Z) a b) (erased (ZLt a b) h) -> (erased (Nat) n) (erased (ZGap a b (Succ n)) g))
  (let-match erased h (MkZLt _ _ pa qa pb qb l r va vb hl hr lt))
  (let ((erased k) (erased hk)) (lt-diff l r lt))
  (values k (zgap-intro a b pa qa pb qb l r (Succ k) va vb hl hr hk)))

(def-fns _ $ (erased zle-gap : (erased (Z) a b) (erased (ZLe a b) h) -> (erased (Nat) n) (erased (ZGap a b n) g))
  (let-match erased h (MkZLe _ _ pa qa pb qb l r va vb hl hr le))
  (let ((erased k) (erased hk)) (lt-diff l (Succ r) le))
  (let ((erased c) (erased e) (erased hc)) (add-succ-right-inv l k (Succ r) hk))
  (let-match erased e (Refl _ _))
  (values k (zgap-intro a b pa qa pb qb l r k va vb hl hr hc)))

(def-fns _ $ (erased zgap-sums : (erased (Z) a b) ->
    (erased (Nat) pa qa pb qb l r) (erased (ZView a pa qa) va) (erased (ZView b pb qb) vb) (erased (Add pa qb l) hl) (erased (Add pb qa r) hr))
  (let ((erased pa) (erased qa) (erased va)) (zview a))
  (let ((erased pb) (erased qb) (erased vb)) (zview b))
  (let ((erased l) (erased hl)) (add pa qb))
  (let ((erased r) (erased hr)) (add pb qa))
  (values pa qa pb qb l r va vb hl hr))

(def-fns _ $ (erased zgap-lt : (erased (Z) a b) (erased (Nat) n) (erased (ZGap a b (Succ n)) g) -> (erased (ZLt a b) h))
  (let ((erased pa) (erased qa) (erased pb) (erased qb) (erased l) (erased r) (erased va) (erased vb) (erased hl) (erased hr)) (zgap-sums a b))
  (MkZLt a b pa qa pb qb l r va vb hl hr (add-pos-lt l (Succ n) r (zgap-elim a b pa qa pb qb l r (Succ n) va vb hl hr g) (LtZ n))))

(def-fns _ $ (erased zgap-le : (erased (Z) a b) (erased (Nat) n) (erased (ZGap a b n) g) -> (erased (ZLe a b) h))
  (let ((erased pa) (erased qa) (erased pb) (erased qb) (erased l) (erased r) (erased va) (erased vb) (erased hl) (erased hr)) (zgap-sums a b))
  (MkZLe a b pa qa pb qb l r va vb hl hr (add-le-left l n r (zgap-elim a b pa qa pb qb l r n va vb hl hr g))))

(def-fns _ $ (erased zof-nat-view : (erased (Z) z) (erased (Nat) n) (erased (ZOf z n (Zero)) o) -> (erased (ZView z n (Zero)) v))
  (let ((erased w) (erased vw)) (znat n))
  (let-match erased (zof-eq z w n (Zero) n (Zero) o (zview-of w n (Zero) vw) (diff-refl n (Zero))) (Refl _ _))
  vw)

(def-fns _ $ (erased znat-add : (erased (Z) d e f) (erased (Nat) n m s) (erased (ZView d n (Zero)) vd) (erased (ZView e m (Zero)) ve)
    (erased (ZAdd d e f) h) (erased (Add n m s) hs) -> (erased (ZView f s (Zero)) v))
  (zof-nat-view f s (zadd-rep d e f n (Zero) m (Zero) s (Zero) h (zview-of d n (Zero) vd) (zview-of e m (Zero) ve) hs (AddZero (Zero)))))

(def-fns _ $ (erased znat-mul : (erased (Z) d e f) (erased (Nat) n m s) (erased (ZView d n (Zero)) vd) (erased (ZView e m (Zero)) ve)
    (erased (ZMul d e f) h) (erased (Mul n m s) hs) -> (erased (ZView f s (Zero)) v))
  (let ((erased z1) (erased k1)) (mul n (Zero)))
  (let-match erased (mul-fn _ _ _ _ k1 (mul-zero-right n)) (Refl _ _))
  (zof-nat-view f s (zmul-rep d e f n (Zero) m (Zero) s (Zero) (Zero) (Zero) s (Zero) h (zview-of d n (Zero) vd) (zview-of e m (Zero) ve)
    hs (MulZero (Zero)) k1 (MulZero m) (add-zero-right s) (AddZero (Zero)))))

(def-fns _ $ (erased zgap-zero : (erased (Z) c) (erased (Nat) n) (erased (ZGap (Z0) c n) g) -> (erased (ZView c n (Zero)) v))
  (let-match erased g (MkZGap _ _ d _ vd h))
  (zof-nat-view c n (zadd-rep (Z0) d c (Zero) (Zero) n (Zero) n (Zero) h (zview-of _ _ _ (ZView0)) (zview-of d n (Zero) vd) (AddZero n) (AddZero (Zero)))))

(def-fns _ $ (erased zgap-refl : (erased (Z) a) -> (erased (ZGap a a (Zero)) g))
  (let ((erased pa) (erased qa) (erased va)) (zview a))
  (let ((erased l) (erased hl)) (add pa qa))
  (zgap-intro a a pa qa pa qa l l (Zero) va va hl hl (add-zero-right l)))

(def-fns _ $ (erased zadd-0-l : (erased (Z) a) -> (erased (ZAdd (Z0) a a) h))
  (let ((erased pa) (erased qa) (erased va)) (zview a))
  (zadd-intro (Z0) a a (Zero) (Zero) pa qa pa qa (ZView0) va (AddZero pa) (AddZero qa) (zview-of a pa qa va)))

(def-fns _ $ (erased zadd-0-r : (erased (Z) a) -> (erased (ZAdd a (Z0) a) h))
  (let ((erased pa) (erased qa) (erased va)) (zview a))
  (zadd-intro a (Z0) a pa qa (Zero) (Zero) pa qa va (ZView0) (add-zero-right pa) (add-zero-right qa) (zview-of a pa qa va)))

(comptime-match many (zring-check (ZEAdd (ZEAdd (zvar 0) (zvar 1)) (ZEAdd (zvar 2) (zvar 3))) (ZEAdd (ZEAdd (zvar 0) (zvar 2)) (ZEAdd (zvar 1) (zvar 3))))
  (Some _ zr-add4))

(def-fns _ $ (erased zgap-add : (erased (Z) a b c d x y) (erased (Nat) n m s) (erased (ZGap a b n) g) (erased (ZGap c d m) k)
    (erased (ZAdd a c x) hx) (erased (ZAdd b d y) hy) (erased (Add n m s) hs) -> (erased (ZGap x y s) r))
  (let-match erased g (MkZGap _ _ e _ ve he))
  (let-match erased k (MkZGap _ _ f _ vf hf))
  (let ((erased w) (erased hw)) (zadd e f))
  (let ((erased y2) (erased hy2)) (zadd x w))
  (let ((erased env)) (Cons _ a $ Cons _ e $ Cons _ c $ Cons _ f $ Nil (Z)))
  (let-match erased (zring-sound env _ _ y y2 zr-add4 (zev-add (zev-add (zev-var 0) (zev-var 1) he) (zev-add (zev-var 2) (zev-var 3) hf) hy)
    (zev-add (zev-add (zev-var 0) (zev-var 2) hx) (zev-add (zev-var 1) (zev-var 3) hw) hy2)) (Refl _ _))
  (MkZGap x y w s (znat-add e f w n m s ve vf hw hs) hy2))

(comptime-match many (zring-check (ZEMul (ZEAdd (zvar 0) (zvar 1)) (zvar 2)) (ZEAdd (ZEMul (zvar 0) (zvar 2)) (ZEMul (zvar 1) (zvar 2))))
  (Some _ zr-distr))

(def-fns _ $ (erased zgap-mul : (erased (Z) a b c x y) (erased (Nat) n m k) (erased (ZGap a b n) g) (erased (ZView c m (Zero)) vc)
    (erased (ZMul a c x) hx) (erased (ZMul b c y) hy) (erased (Mul n m k) hk) -> (erased (ZGap x y k) r))
  (let-match erased g (MkZGap _ _ e _ ve he))
  (let ((erased w) (erased hw)) (zmul e c))
  (let ((erased y2) (erased hy2)) (zadd x w))
  (let ((erased env)) (Cons _ a $ Cons _ e $ Cons _ c $ Nil (Z)))
  (let-match erased (zring-sound env _ _ y y2 zr-distr (zev-mul (zev-add (zev-var 0) (zev-var 1) he) (zev-var 2) hy)
    (zev-add (zev-mul (zev-var 0) (zev-var 2) hx) (zev-mul (zev-var 1) (zev-var 2) hw) hy2)) (Refl _ _))
  (MkZGap x y w k (znat-mul e c w n m k ve vc hw hk) hy2))

(def-fns _ $ (erased zgap-trans : (erased (Z) a b c) (erased (Nat) n m s) (erased (ZGap a b n) g) (erased (ZGap b c m) k) (erased (Add n m s) hs)
    -> (erased (ZGap a c s) r))
  (let-match erased k (MkZGap _ _ e _ ve he))
  (zgap-add a b (Z0) e a c n m s g (MkZGap (Z0) e e m ve (zadd-0-l e)) (zadd-0-r a) he hs))

(def-fns _ $ (erased zgap-0 : (erased (Z) a b) (erased (ZGap a b (Zero)) g) -> (erased (Eq (Z) a b) e))
  (let-match erased g (MkZGap _ _ d _ vd h))
  (let-match erased vd (ZView0))
  (zadd-fn a (Z0) a b (zadd-0-r a) h))

(def-fns _ $ (erased zlt-trans : (erased (Z) a b c) (erased (ZLt a b) h) (erased (ZLt b c) k) -> (erased (ZLt a c) r))
  (let ((erased n) (erased g1)) (zlt-gap a b h))
  (let ((erased m) (erased g2)) (zlt-gap b c k))
  (let ((erased s) (erased hs)) (add n (Succ m)))
  (zgap-lt a c s (zgap-trans a b c (Succ n) (Succ m) (Succ s) g1 g2 (AddSucc n (Succ m) s hs))))

(def-fns _ $ (erased zle-trans : (erased (Z) a b c) (erased (ZLe a b) h) (erased (ZLe b c) k) -> (erased (ZLe a c) r))
  (let ((erased n) (erased g1)) (zle-gap a b h))
  (let ((erased m) (erased g2)) (zle-gap b c k))
  (let ((erased s) (erased hs)) (add n m))
  (zgap-le a c s (zgap-trans a b c n m s g1 g2 hs)))

(def-fns _ $ (erased zlt-le-trans : (erased (Z) a b c) (erased (ZLt a b) h) (erased (ZLe b c) k) -> (erased (ZLt a c) r))
  (let ((erased n) (erased g1)) (zlt-gap a b h))
  (let ((erased m) (erased g2)) (zle-gap b c k))
  (let ((erased s) (erased hs)) (add n m))
  (zgap-lt a c s (zgap-trans a b c (Succ n) m (Succ s) g1 g2 (AddSucc n m s hs))))

(def-fns _ $ (erased zle-lt-trans : (erased (Z) a b c) (erased (ZLe a b) h) (erased (ZLt b c) k) -> (erased (ZLt a c) r))
  (let ((erased n) (erased g1)) (zle-gap a b h))
  (let ((erased m) (erased g2)) (zlt-gap b c k))
  (let ((erased s) (erased hs)) (add n m))
  (zgap-lt a c s (zgap-trans a b c n (Succ m) (Succ s) g1 g2 (add-succ-right n m s hs))))

(def-fns _ $ (erased zle-refl : (erased (Z) a) -> (erased (ZLe a a) h))
  (zgap-le a a (Zero) (zgap-refl a)))

(def-fns _ $ (erased zlt-le-incl : (erased (Z) a b) (erased (ZLt a b) h) -> (erased (ZLe a b) k))
  (let ((erased n) (erased g)) (zlt-gap a b h))
  (zgap-le a b (Succ n) g))

(def-fns _ $ (erased zlt-irrefl : (erased (Z) a) (erased (ZLt a a) h) -> (erased (False) f))
  (let-match erased h (MkZLt _ _ pa qa pb qb l r va vb hl hr lt))
  (let ((erased e1) (erased e2)) (zview-fn a pa qa pb qb va vb))
  (let-match erased e1 (Refl _ _))
  (let-match erased e2 (Refl _ _))
  (let-match erased (add-fn pa qa l r hl hr) (Refl _ _))
  (lt-irrefl l lt))

(def-fns _ $ (erased zle-ngt : (erased (Z) a b) (erased (ZLe a b) h) (erased (ZLt b a) k) -> (erased (False) f))
  (zlt-irrefl a (zle-lt-trans a b a h k)))

(def-fns _ $ (erased zle-lteq : (erased (Z) a b) (erased (ZLe a b) h) -> (erased (Le (Z) ZLt a b) k))
  (let ((erased n) (erased g)) (zle-gap a b h))
  (let-match erased n (Zero) ((Succ n1) (LeLt _ _ a b (zgap-lt a b n1 g))))
  (let-match erased (zgap-0 a b g) (Refl _ _))
  (LeEq _ _ a))

(def-fns _ $ (erased zlteq-le : (erased (Z) a b) (erased (Le (Z) ZLt a b) h) -> (erased (ZLe a b) k))
  (match erased h _ ((LeLt _ _ _ _ lt) (zlt-le-incl a b lt)) ((LeEq _ _ _) (zle-refl a))))

(def-fns _ $ (erased zle-antisymm : (erased (Z) a b) (erased (ZLe a b) h) (erased (ZLe b a) k) -> (erased (Eq (Z) a b) e))
  (match erased (zle-lteq a b h) _
    ((LeEq _ _ _) (Refl _ a))
    (absurd (LeLt _ _ _ _ lt) (zle-ngt b a k lt))))

(def-fns _ $ (many ztrichotomy-inf : (many (Z) a b) -> (many (Cmp (Z) ZLt a b) c))
  (let ((many pa) (many qa) (erased va)) (zview a))
  (let ((many pb) (many qb) (erased vb)) (zview b))
  (let ((many l) (erased hl)) (add pa qb))
  (let ((many r) (erased hr)) (add pb qa))
  (let-match many (nat-cmp l r) (CEq _ _ _)
    ((CLt _ _ _ _ lt) (CLt _ _ a b (MkZLt a b pa qa pb qb l r va vb hl hr lt)))
    ((CGt _ _ _ _ gt) (CGt _ _ a b (MkZLt b a pb qb pa qa r l vb va hr hl gt))))
  (let-match erased (zview-diff a b pa qa pb qb va vb (MkDiffEq pa qa pb qb l hl hr)) (Refl _ _))
  (CEq _ _ a))

(def-adts $ (LtLe : (Type T) ((TyCtor (T x) (T y) -> Type) R) ((TyCtor (T x) (T y) -> Type) S) (T a) (T b) -> Type)
  enum
  (many IsLt : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R S) (erased T a b) (erased (R a b) p) -> (LtLe T R S a b))
  (many IsGe : (erased Type T) (erased (TyCtor (T x) (T y) -> Type) R S) (erased T a b) (erased (S b a) p) -> (LtLe T R S a b)))

(def-fns _ $ (many zlt-le-dec : (many (Z) a b) -> (many (LtLe (Z) ZLt ZLe a b) d))
  (match many (ztrichotomy-inf a b) _
    ((CLt _ _ _ _ lt) (IsLt _ _ _ a b lt))
    ((CEq _ _ _) (IsGe _ _ _ a b (zle-refl a)))
    ((CGt _ _ _ _ gt) (IsGe _ _ _ a b (zlt-le-incl b a gt)))))

(def-fns _ $ (many zmax : (many (Z) a b) -> (many (Z) c) (erased (ZMax a b c) h))
  (match many (zlt-le-dec a b) _
    ((IsLt _ _ _ _ _ lt) (values b (ZMaxRight a b lt)))
    ((IsGe _ _ _ _ _ le) (values a (ZMaxLeft a b le)))))

(def-fns _ $ (erased zmax-fn : (erased (Z) a b c d) (erased (ZMax a b c) h) (erased (ZMax a b d) k) -> (erased (Eq (Z) c d) e))
  (match erased h _
    ((ZMaxLeft _ _ le) (match erased k _ ((ZMaxLeft _ _ _) (Refl _ c)) (absurd (ZMaxRight _ _ lt) (zle-ngt b a le lt))))
    ((ZMaxRight _ _ lt) (match erased k _ ((ZMaxRight _ _ _) (Refl _ c)) (absurd (ZMaxLeft _ _ le) (zle-ngt b a le lt))))))

(def-fns _ $ (erased zadd-lt-mono : (erased (Z) a b c d x y) (erased (ZLt a b) h) (erased (ZLt c d) k) (erased (ZAdd a c x) hx) (erased (ZAdd b d y) hy)
    -> (erased (ZLt x y) r))
  (let ((erased n) (erased g1)) (zlt-gap a b h))
  (let ((erased m) (erased g2)) (zlt-gap c d k))
  (let ((erased s) (erased hs)) (add n (Succ m)))
  (zgap-lt x y s (zgap-add a b c d x y (Succ n) (Succ m) (Succ s) g1 g2 hx hy (AddSucc n (Succ m) s hs))))

(def-fns _ $ (erased zadd-le-mono : (erased (Z) a b c d x y) (erased (ZLe a b) h) (erased (ZLe c d) k) (erased (ZAdd a c x) hx) (erased (ZAdd b d y) hy)
    -> (erased (ZLe x y) r))
  (let ((erased n) (erased g1)) (zle-gap a b h))
  (let ((erased m) (erased g2)) (zle-gap c d k))
  (let ((erased s) (erased hs)) (add n m))
  (zgap-le x y s (zgap-add a b c d x y n m s g1 g2 hx hy hs)))

(def-fns _ $ (erased zadd-lt-le-mono : (erased (Z) a b c d x y) (erased (ZLt a b) h) (erased (ZLe c d) k) (erased (ZAdd a c x) hx) (erased (ZAdd b d y) hy)
    -> (erased (ZLt x y) r))
  (let ((erased n) (erased g1)) (zlt-gap a b h))
  (let ((erased m) (erased g2)) (zle-gap c d k))
  (let ((erased s) (erased hs)) (add n m))
  (zgap-lt x y s (zgap-add a b c d x y (Succ n) m (Succ s) g1 g2 hx hy (AddSucc n m s hs))))

(def-fns _ $ (erased zadd-le-lt-mono : (erased (Z) a b c d x y) (erased (ZLe a b) h) (erased (ZLt c d) k) (erased (ZAdd a c x) hx) (erased (ZAdd b d y) hy)
    -> (erased (ZLt x y) r))
  (let ((erased n) (erased g1)) (zle-gap a b h))
  (let ((erased m) (erased g2)) (zlt-gap c d k))
  (let ((erased s) (erased hs)) (add n m))
  (zgap-lt x y s (zgap-add a b c d x y n (Succ m) (Succ s) g1 g2 hx hy (add-succ-right n m s hs))))

(def-fns _ $ (erased zadd-lt-mono-r : (erased (Z) a b c x y) (erased (ZLt a b) h) (erased (ZAdd a c x) hx) (erased (ZAdd b c y) hy) -> (erased (ZLt x y) r))
  (zadd-lt-le-mono a b c c x y h (zle-refl c) hx hy))

(def-fns _ $ (erased zadd-le-mono-r : (erased (Z) a b c x y) (erased (ZLe a b) h) (erased (ZAdd a c x) hx) (erased (ZAdd b c y) hy) -> (erased (ZLe x y) r))
  (zadd-le-mono a b c c x y h (zle-refl c) hx hy))

(def-fns _ $ (erased zadd-lt-mono-l : (erased (Z) a b c x y) (erased (ZLt a b) h) (erased (ZAdd c a x) hx) (erased (ZAdd c b y) hy) -> (erased (ZLt x y) r))
  (zadd-le-lt-mono c c a b x y (zle-refl c) h hx hy))

(def-fns _ $ (erased zadd-le-mono-l : (erased (Z) a b c x y) (erased (ZLe a b) h) (erased (ZAdd c a x) hx) (erased (ZAdd c b y) hy) -> (erased (ZLe x y) r))
  (zadd-le-mono c c a b x y (zle-refl c) h hx hy))

(comptime-match many (zring-check (ZEAdd (zvar 0) (zvar 1)) (ZEAdd (zvar 1) (zvar 0))) (Some _ zr-add-comm))
(comptime-match many (zring-check (ZEMul (zvar 0) (zvar 1)) (ZEMul (zvar 1) (zvar 0))) (Some _ zr-mul-comm))

(def-fns _ $ (erased zadd-comm : (erased (Z) a b c) (erased (ZAdd a b c) h) -> (erased (ZAdd b a c) k))
  (let ((erased d) (erased k)) (zadd b a))
  (let ((erased env)) (Cons _ a $ Cons _ b $ Nil (Z)))
  (let-match erased (zring-sound env _ _ c d zr-add-comm (zev-add (zev-var 0) (zev-var 1) h) (zev-add (zev-var 1) (zev-var 0) k)) (Refl _ _))
  k)

(def-fns _ $ (erased zmul-comm : (erased (Z) a b c) (erased (ZMul a b c) h) -> (erased (ZMul b a c) k))
  (let ((erased d) (erased k)) (zmul b a))
  (let ((erased env)) (Cons _ a $ Cons _ b $ Nil (Z)))
  (let-match erased (zring-sound env _ _ c d zr-mul-comm (zev-mul (zev-var 0) (zev-var 1) h) (zev-mul (zev-var 1) (zev-var 0) k)) (Refl _ _))
  k)

(def-fns _ $ (erased zmul-lt-mono-pos-r : (erased (Z) a b c x y) (erased (ZLt (Z0) c) hc) (erased (ZLt a b) h) (erased (ZMul a c x) hx) (erased (ZMul b c y) hy)
    -> (erased (ZLt x y) r))
  (let ((erased k) (erased gc)) (zlt-gap (Z0) c hc))
  (let ((erased n) (erased g)) (zlt-gap a b h))
  (let ((erased m) (erased hm)) (mul n (Succ k)))
  (let ((erased p) (erased hp)) (add m k))
  (zgap-lt x y p (zgap-mul a b c x y (Succ n) (Succ k) (Succ p) g (zgap-zero c (Succ k) gc) hx hy
    (MulSucc n (Succ k) m (Succ p) hm (add-succ-right m k p hp)))))

(def-fns _ $ (erased zmul-le-mono-nonneg-r : (erased (Z) a b c x y) (erased (ZLe (Z0) c) hc) (erased (ZLe a b) h) (erased (ZMul a c x) hx) (erased (ZMul b c y) hy)
    -> (erased (ZLe x y) r))
  (let ((erased k) (erased gc)) (zle-gap (Z0) c hc))
  (let ((erased n) (erased g)) (zle-gap a b h))
  (let ((erased m) (erased hm)) (mul n k))
  (zgap-le x y m (zgap-mul a b c x y n k m g (zgap-zero c k gc) hx hy hm)))

(def-fns _ $ (erased zmul-lt-mono-pos-l : (erased (Z) a b c x y) (erased (ZLt (Z0) c) hc) (erased (ZLt a b) h) (erased (ZMul c a x) hx) (erased (ZMul c b y) hy)
    -> (erased (ZLt x y) r))
  (zmul-lt-mono-pos-r a b c x y hc h (zmul-comm c a x hx) (zmul-comm c b y hy)))

(def-fns _ $ (erased zmul-le-mono-nonneg-l : (erased (Z) a b c x y) (erased (ZLe (Z0) c) hc) (erased (ZLe a b) h) (erased (ZMul c a x) hx) (erased (ZMul c b y) hy)
    -> (erased (ZLe x y) r))
  (zmul-le-mono-nonneg-r a b c x y hc h (zmul-comm c a x hx) (zmul-comm c b y hy)))

(def-fns _ $ (erased zgap-nat : (erased (Z) z) (erased (Nat) n) (erased (ZView z n (Zero)) v) -> (erased (ZGap (Z0) z n) g))
  (MkZGap (Z0) z z n v (zadd-0-l z)))

(def-fns _ $ (erased zpos-is-pos : (erased (Nat) p) -> (erased (ZLt (Z0) (Zpos p)) h))
  (zgap-lt (Z0) (Zpos p) p (zgap-nat (Zpos p) (Succ p) (ZViewPos p))))

(def-fns _ $ (erased znat-nonneg : (erased (Z) z) (erased (Nat) n) (erased (ZView z n (Zero)) v) -> (erased (ZLe (Z0) z) h))
  (zgap-le (Z0) z n (zgap-nat z n v)))

(comptime-match many (zring-check (zvar 0) (ZEAdd (ZEAdd (zvar 0) (zvar 1)) (ZEOpp (zvar 1)))) (Some _ zr-add-opp))

(def-fns _ $ (erased zadd-reg-r : (erased (Z) a b c x) (erased (ZAdd a c x) h) (erased (ZAdd b c x) k) -> (erased (Eq (Z) a b) e))
  (let ((erased o) (erased ho)) (zopp c))
  (let ((erased v) (erased hv)) (zadd x o))
  (let ((erased ea)) (zring-sound (Cons _ a $ Cons _ c $ Nil (Z)) _ _ a v zr-add-opp (zev-var 0) (zev-add (zev-add (zev-var 0) (zev-var 1) h) (zev-opp (zev-var 1) ho) hv)))
  (let ((erased eb)) (zring-sound (Cons _ b $ Cons _ c $ Nil (Z)) _ _ b v zr-add-opp (zev-var 0) (zev-add (zev-add (zev-var 0) (zev-var 1) k) (zev-opp (zev-var 1) ho) hv)))
  (let-match erased ea (Refl _ _))
  (let-match erased eb (Refl _ _))
  (Refl _ a))

(def-fns _ $ (erased zadd-lt-reg-r : (erased (Z) a b c x y) (erased (ZAdd a c x) hx) (erased (ZAdd b c y) hy) (erased (ZLt x y) h) -> (erased (ZLt a b) r))
  (let-match erased (zlt-le-dec a b) (IsLt _ _ _ _ _ lt)
    (absurd (IsGe _ _ _ _ _ le) (zle-ngt y x (zadd-le-mono-r b a c y x le hy hx) h)))
  lt)

(def-fns _ $ (erased zadd-le-reg-r : (erased (Z) a b c x y) (erased (ZAdd a c x) hx) (erased (ZAdd b c y) hy) (erased (ZLe x y) h) -> (erased (ZLe a b) r))
  (let-match erased (zlt-le-dec b a) (IsGe _ _ _ _ _ le)
    (absurd (IsLt _ _ _ _ _ lt) (zle-ngt x y h (zadd-lt-mono-r b a c y x lt hy hx))))
  le)

(def-fns _ $ (erased zmul-reg-r : (erased (Z) a b c x) (erased (ZLt (Z0) c) hc) (erased (ZMul a c x) h) (erased (ZMul b c x) k) -> (erased (Eq (Z) a b) e))
  (let-match erased (ztrichotomy-inf a b) (CEq _ _ _)
    (absurd (CLt _ _ _ _ lt) (zlt-irrefl x (zmul-lt-mono-pos-r a b c x x hc lt h k)))
    (absurd (CGt _ _ _ _ gt) (zlt-irrefl x (zmul-lt-mono-pos-r b a c x x hc gt k h))))
  (Refl _ a))

(def-fns _ $ (erased zmul-lt-reg-r : (erased (Z) a b c x y) (erased (ZLt (Z0) c) hc) (erased (ZMul a c x) hx) (erased (ZMul b c y) hy) (erased (ZLt x y) h)
    -> (erased (ZLt a b) r))
  (let-match erased (zlt-le-dec a b) (IsLt _ _ _ _ _ lt)
    (absurd (IsGe _ _ _ _ _ le) (zle-ngt y x (zmul-le-mono-nonneg-r b a c y x (zlt-le-incl _ _ hc) le hy hx) h)))
  lt)

(def-fns _ $ (erased zmul-le-reg-r : (erased (Z) a b c x y) (erased (ZLt (Z0) c) hc) (erased (ZMul a c x) hx) (erased (ZMul b c y) hy) (erased (ZLe x y) h)
    -> (erased (ZLe a b) r))
  (let-match erased (zlt-le-dec b a) (IsGe _ _ _ _ _ le)
    (absurd (IsLt _ _ _ _ _ lt) (zle-ngt x y h (zmul-lt-mono-pos-r b a c y x hc lt hy hx))))
  le)

(def-fns _ $ (erased zring-sums : (erased (List (Z)) env) (erased (ZExpr) p q s t) (erased (Z) zp zq zs zt)
    (erased (ZRingEq (ZEAdd p s) (ZEAdd q t)) h) (erased (ZEval env p zp) ep) (erased (ZEval env q zq) eq)
    (erased (ZEval env s zs) es) (erased (ZEval env t zt) et) -> (erased (Z) x) (erased (ZAdd zp zs x) hp) (erased (ZAdd zq zt x) hq))
  (let ((erased x) (erased hp)) (zadd zp zs))
  (let ((erased y) (erased hq)) (zadd zq zt))
  (let-match erased (zring-sound env _ _ x y h (ZEvAdd env p s zp zs x ep es hp) (ZEvAdd env q t zq zt y eq et hq)) (Refl _ _))
  (values x hp hq))

(def-fns _ $ (erased zring-eq : (erased (List (Z)) env) (erased (ZExpr) p q s t) (erased (Z) zp zq zs)
    (erased (ZRingEq (ZEAdd p s) (ZEAdd q t)) h) (erased (ZEval env p zp) ep) (erased (ZEval env q zq) eq)
    (erased (ZEval env s zs) es) (erased (ZEval env t zs) et) -> (erased (Eq (Z) zp zq) e))
  (let ((erased x) (erased hp) (erased hq)) (zring-sums env p q s t zp zq zs zs h ep eq es et))
  (zadd-reg-r zp zq zs x hp hq))

(def-adts $ (ZPm : ((Z) a) ((Z) b) -> Type)
  enum
  (many ZPmSame : (erased (Z) a) -> (ZPm a a))
  (many ZPmOpp : (erased (Z) a b) (erased (ZOpp a b) h) -> (ZPm a b)))


(def-fns _ $ (erased zneg-is-neg : (erased (Nat) p) -> (erased (ZLt (Zneg p) (Z0)) h))
  (MkZLt _ _ (Zero) (Succ p) (Zero) (Zero) (Zero) (Succ p) (ZViewNeg p) (ZView0) (AddZero _) (AddZero _) (LtZ p)))

(def-fns _ $ (erased zabs-pm : (erased (Z) a b) (erased (ZAbs a b) h) -> (erased (ZPm a b) s) (erased (ZLe (Z0) b) le))
  (match erased h _
    ((ZAbs0) (values (ZPmSame a) (zle-refl _)))
    ((ZAbsPos p) (values (ZPmSame a) (zlt-le-incl _ _ (zpos-is-pos p))))
    ((ZAbsNeg p) (values (ZPmOpp a b (ZOppNeg p)) (zlt-le-incl _ _ (zpos-is-pos p))))))

(def-fns _ $ (erased zabs-unique : (erased (Z) a b c) (erased (ZPm a b) s) (erased (ZLe (Z0) b) le) (erased (ZAbs a c) h) -> (erased (Eq (Z) c b) e))
  (match erased h _
    ((ZAbs0) (let-match erased s (ZPmOpp _ _ o) ((ZPmSame _) (Refl _ c))) (let-match erased o (ZOpp0)) (Refl _ c))
    ((ZAbsPos p) (let-match erased s (ZPmSame _) (absurd (ZPmOpp _ _ o) (let-match erased o (ZOppPos _)) (zle-ngt _ _ le (zneg-is-neg p)))) (Refl _ c))
    ((ZAbsNeg p)
      (let-match erased s (ZPmOpp _ _ o) (absurd (ZPmSame _) (zle-ngt _ _ le (zneg-is-neg p))))
      (let-match erased o (ZOppNeg _))
      (Refl _ c))))

(comptime-match many (zring-check (ZEMul (ZEOpp (zvar 0)) (zvar 1)) (ZEOpp (ZEMul (zvar 0) (zvar 1)))) (Some _ zr-opp-mul))
(comptime-match many (zring-check (ZEOpp (ZEOpp (zvar 0))) (zvar 0)) (Some _ zr-opp-opp))

(def-fns _ $ (erased zopp-mul-l : (erased (Z) a b c o d) (erased (ZOpp a o) ho) (erased (ZMul a b c) h) (erased (ZMul o b d) k) -> (erased (ZOpp c d) r))
  (let ((erased w) (erased hw)) (zopp c))
  (let-match erased (zring-sound (Cons _ a $ Cons _ b $ Nil (Z)) _ _ d w zr-opp-mul (zev-mul (zev-opp (zev-var 0) ho) (zev-var 1) k) (zev-opp (zev-mul (zev-var 0) (zev-var 1) h) hw))
    (Refl _ _))
  hw)

(def-fns _ $ (erased zopp-opp : (erased (Z) a b c) (erased (ZOpp a b) h) (erased (ZOpp b c) k) -> (erased (Eq (Z) c a) e))
  (zring-sound (Cons _ a $ Nil (Z)) _ _ c a zr-opp-opp (zev-opp (zev-opp (zev-var 0) h) k) (zev-var 0)))

(def-fns _ $ (erased zopp-sym : (erased (Z) a b) (erased (ZOpp a b) h) -> (erased (ZOpp b a) k))
  (match erased h _ ((ZOpp0) (ZOpp0)) ((ZOppPos p) (ZOppNeg p)) ((ZOppNeg p) (ZOppPos p))))

(def-fns _ $ (erased zpm-mul : (erased (Z) a b c a2 b2 d) (erased (ZPm a a2) s) (erased (ZPm b b2) t) (erased (ZMul a b c) h) (erased (ZMul a2 b2 d) k)
    -> (erased (ZPm c d) r))
  (match erased s _
    ((ZPmSame _)
      (let-match erased t (ZPmSame _) ((ZPmOpp _ _ o) (ZPmOpp c d (zopp-mul-l b a c b2 d o (zmul-comm _ _ _ h) (zmul-comm _ _ _ k)))))
      (let-match erased (zmul-fn _ _ _ _ h k) (Refl _ _))
      (ZPmSame c))
    ((ZPmOpp _ _ o)
      (let-match erased t (ZPmOpp _ _ o2) ((ZPmSame _) (ZPmOpp c d (zopp-mul-l a b c a2 d o h k))))
      (let ((erased e) (erased he)) (zmul a2 b))
      (let ((erased f)) (zopp-mul-l a b c a2 e o h he))
      (let ((erased g)) (zopp-mul-l b a2 e b2 d o2 (zmul-comm _ _ _ he) (zmul-comm _ _ _ k)))
      (let-match erased (zopp-opp _ _ _ f g) (Refl _ _))
      (ZPmSame c))))

(def-fns _ $ (erased zmul-0-l : (erased (Z) a) -> (erased (ZMul (Z0) a (Z0)) h))
  (let ((erased pa) (erased qa) (erased va)) (zview a))
  (zmul-intro (Z0) a (Z0) (Zero) (Zero) pa qa (Zero) (Zero) (Zero) (Zero) (Zero) (Zero) (ZView0) va
    (MulZero _) (MulZero _) (MulZero _) (MulZero _) (AddZero _) (AddZero _) (zview-of _ _ _ (ZView0))))

(def-fns _ $ (erased zmul-nonneg : (erased (Z) a b c) (erased (ZLe (Z0) a) ha) (erased (ZLe (Z0) b) hb) (erased (ZMul a b c) h) -> (erased (ZLe (Z0) c) r))
  (zmul-le-mono-nonneg-r (Z0) a b (Z0) c hb ha (zmul-0-l b) h))

(def-fns _ $ (erased zabs-mul : (erased (Z) a b c a2 b2 c2 d) (erased (ZMul a b c) h) (erased (ZAbs a a2) ha) (erased (ZAbs b b2) hb) (erased (ZAbs c c2) hc)
    (erased (ZMul a2 b2 d) k) -> (erased (Eq (Z) c2 d) e))
  (let ((erased sa) (erased la)) (zabs-pm a a2 ha))
  (let ((erased sb) (erased lb)) (zabs-pm b b2 hb))
  (zabs-unique c d c2 (zpm-mul a b c a2 b2 d sa sb h k) (zmul-nonneg a2 b2 d la lb k) hc))

(def-fns _ $ (erased zle-abs : (erased (Z) a b) (erased (ZAbs a b) h) -> (erased (ZLe a b) r))
  (match erased h _
    ((ZAbs0) (zle-refl _))
    ((ZAbsPos _) (zle-refl _))
    ((ZAbsNeg p) (zlt-le-incl _ _ (zlt-trans _ _ _ (zneg-is-neg p) (zpos-is-pos p))))))

(def-fns _ $ (erased zopp-le-abs : (erased (Z) a b o) (erased (ZAbs a b) h) (erased (ZOpp a o) k) -> (erased (ZLe o b) r))
  (let ((erased k2)) (zopp-sym a o k))
  (zle-abs o b (match erased h (((ZAbs o b) r))
    ((ZAbs0) (let-match erased k2 (ZOpp0)) (ZAbs0))
    ((ZAbsPos p) (let-match erased k2 (ZOppNeg _)) (ZAbsNeg p))
    ((ZAbsNeg p) (let-match erased k2 (ZOppPos _)) (ZAbsPos p)))))

(comptime-match many (zring-check (ZEAdd (ZEOpp (ZEAdd (zvar 0) (zvar 1))) (zvar 1)) (ZEOpp (zvar 0))) (Some _ zr-opp-gap))

(def-fns _ $ (erased zgap-opp : (erased (Z) a b a2 b2) (erased (Nat) n) (erased (ZGap a b n) g) (erased (ZOpp a a2) ha) (erased (ZOpp b b2) hb)
    -> (erased (ZGap b2 a2 n) r))
  (let-match erased g (MkZGap _ _ d _ vd h))
  (let ((erased w) (erased hw)) (zadd b2 d))
  (let-match erased (zring-sound (Cons _ a $ Cons _ d $ Nil (Z)) _ _ w a2 zr-opp-gap (zev-add (zev-opp (zev-add (zev-var 0) (zev-var 1) h) hb) (zev-var 1) hw)
    (zev-opp (zev-var 0) ha)) (Refl _ _))
  (MkZGap b2 a2 d n vd hw))

(def-fns _ $ (erased zopp-lt-mono : (erased (Z) a b a2 b2) (erased (ZLt a b) h) (erased (ZOpp a a2) ha) (erased (ZOpp b b2) hb) -> (erased (ZLt b2 a2) r))
  (let ((erased n) (erased g)) (zlt-gap a b h))
  (zgap-lt b2 a2 n (zgap-opp a b a2 b2 (Succ n) g ha hb)))

(def-fns _ $ (erased zopp-le-mono : (erased (Z) a b a2 b2) (erased (ZLe a b) h) (erased (ZOpp a a2) ha) (erased (ZOpp b b2) hb) -> (erased (ZLe b2 a2) r))
  (let ((erased n) (erased g)) (zle-gap a b h))
  (zgap-le b2 a2 n (zgap-opp a b a2 b2 n g ha hb)))

(def-fns _ $ (erased zabs-le : (erased (Z) a b o e) (erased (ZLe a e) h1) (erased (ZOpp a o) k) (erased (ZLe o e) h2) (erased (ZAbs a b) h) -> (erased (ZLe b e) r))
  (let ((erased s) (erased _)) (zabs-pm a b h))
  (let-match erased s (ZPmOpp _ _ k2) ((ZPmSame _) h1))
  (let-match erased (zopp-fn a o b k k2) (Refl _ _))
  h2)

(def-fns _ $ (erased zabs-lt : (erased (Z) a b o e) (erased (ZLt a e) h1) (erased (ZOpp a o) k) (erased (ZLt o e) h2) (erased (ZAbs a b) h) -> (erased (ZLt b e) r))
  (let ((erased s) (erased _)) (zabs-pm a b h))
  (let-match erased s (ZPmOpp _ _ k2) ((ZPmSame _) h1))
  (let-match erased (zopp-fn a o b k k2) (Refl _ _))
  h2)

(comptime-match many (zring-check (ZEOpp (ZEAdd (zvar 0) (zvar 1))) (ZEAdd (ZEOpp (zvar 0)) (ZEOpp (zvar 1)))) (Some _ zr-opp-add))

(def-fns _ $ (erased zopp-add : (erased (Z) a b c a2 b2 c2) (erased (ZAdd a b c) h) (erased (ZOpp a a2) ha) (erased (ZOpp b b2) hb) (erased (ZOpp c c2) hc)
    -> (erased (ZAdd a2 b2 c2) r))
  (let ((erased w) (erased hw)) (zadd a2 b2))
  (let-match erased (zring-sound (Cons _ a $ Cons _ b $ Nil (Z)) _ _ c2 w zr-opp-add (zev-opp (zev-add (zev-var 0) (zev-var 1) h) hc)
    (zev-add (zev-opp (zev-var 0) ha) (zev-opp (zev-var 1) hb) hw)) (Refl _ _))
  hw)

(def-fns _ $ (erased zabs-triangle : (erased (Z) a b c a2 b2 c2 s) (erased (ZAdd a b c) h) (erased (ZAbs a a2) ha) (erased (ZAbs b b2) hb)
    (erased (ZAbs c c2) hc) (erased (ZAdd a2 b2 s) hs) -> (erased (ZLe c2 s) r))
  (let ((erased oa) (erased hoa)) (zopp a))
  (let ((erased ob) (erased hob)) (zopp b))
  (let ((erased oc) (erased hoc)) (zopp c))
  (zabs-le c c2 oc s (zadd-le-mono a a2 b b2 c s (zle-abs a a2 ha) (zle-abs b b2 hb) h hs) hoc
    (zadd-le-mono oa a2 ob b2 oc s (zopp-le-abs a a2 oa ha hoa) (zopp-le-abs b b2 ob hb hob) (zopp-add a b c oa ob oc h hoa hob hoc) hs) hc))

(def-fns _ $ (erased zabs-lt-l : (erased (Z) a b e) (erased (ZAbs a b) h) (erased (ZLt b e) lt) -> (erased (ZLt a e) r))
  (zle-lt-trans a b e (zle-abs a b h) lt))

(def-fns _ $ (erased zabs-lt-r : (erased (Z) a b e o) (erased (ZAbs a b) h) (erased (ZLt b e) lt) (erased (ZOpp e o) k) -> (erased (ZLt o a) r))
  (let ((erased oa) (erased hoa)) (zopp a))
  (let ((erased oo) (erased hoo)) (zopp oa))
  (let-match erased (zopp-opp _ _ _ hoa hoo) (Refl _ _))
  (zopp-lt-mono oa e oo o (zle-lt-trans oa b e (zopp-le-abs a b oa h hoa) lt) hoo k))

(def-fns _ $ (erased zabs-lt-intro : (erased (Z) a b e o) (erased (ZLt a e) h1) (erased (ZOpp e o) k) (erased (ZLt o a) h2) (erased (ZAbs a b) h)
    -> (erased (ZLt b e) r))
  (let ((erased oa) (erased hoa)) (zopp a))
  (zabs-lt a b oa e h1 hoa (zopp-lt-mono o a e oa h2 (zopp-sym e o k) hoa) h))

(def-fns _ $ (erased zabs-nonneg : (erased (Z) a b) (erased (ZAbs a b) h) -> (erased (ZLe (Z0) b) r))
  (let ((erased _) (erased le)) (zabs-pm a b h))
  le)

(def-adts $ (ORel : -> Type)
  enum
  (many OLt : -> (ORel))
  (many OLe : -> (ORel)))

(def-adts $ (OMeet : ((ORel) k1) ((ORel) k2) ((ORel) k) -> Type)
  enum
  (many OMeetLt : (erased (ORel) k) -> (OMeet (OLt) k (OLt)))
  (many OMeetLe : (erased (ORel) k) -> (OMeet (OLe) k k)))

(def-fns _ $ (erased omeet : (erased (ORel) k1 k2) -> (erased (ORel) k) (erased (OMeet k1 k2 k) m))
  (match erased k1 _ ((OLt) (values (OLt) (OMeetLt k2))) ((OLe) (values k2 (OMeetLe k2)))))

(def-adts $ (ZR : ((ORel) k) ((Z) a) ((Z) b) -> Type)
  enum
  (many ZRLt : (erased (Z) a b) (erased (ZLt a b) h) -> (ZR (OLt) a b))
  (many ZRLe : (erased (Z) a b) (erased (ZLe a b) h) -> (ZR (OLe) a b)))

(def-fns _ $ (erased zr-le : (erased (ORel) k) (erased (Z) a b) (erased (ZR k a b) h) -> (erased (ZLe a b) r))
  (match erased h _ ((ZRLt _ _ lt) (zlt-le-incl a b lt)) ((ZRLe _ _ le) le)))

(def-fns _ $ (erased zr-mul-pos-r : (erased (ORel) k) (erased (Z) a b c x y) (erased (ZLt (Z0) c) hc) (erased (ZR k a b) h)
    (erased (ZMul a c x) hx) (erased (ZMul b c y) hy) -> (erased (ZR k x y) r))
  (match erased h _
    ((ZRLt _ _ lt) (ZRLt x y (zmul-lt-mono-pos-r a b c x y hc lt hx hy)))
    ((ZRLe _ _ le) (ZRLe x y (zmul-le-mono-nonneg-r a b c x y (zlt-le-incl _ _ hc) le hx hy)))))

(def-fns _ $ (erased zr-mul-pos-l : (erased (ORel) k) (erased (Z) a b c x y) (erased (ZLt (Z0) c) hc) (erased (ZR k a b) h)
    (erased (ZMul c a x) hx) (erased (ZMul c b y) hy) -> (erased (ZR k x y) r))
  (zr-mul-pos-r k a b c x y hc h (zmul-comm _ _ _ hx) (zmul-comm _ _ _ hy)))

(def-fns _ $ (erased zr-mul-reg-r : (erased (ORel) k) (erased (Z) a b c x y) (erased (ZLt (Z0) c) hc)
    (erased (ZMul a c x) hx) (erased (ZMul b c y) hy) (erased (ZR k x y) h) -> (erased (ZR k a b) r))
  (match erased h _
    ((ZRLt _ _ lt) (ZRLt a b (zmul-lt-reg-r a b c x y hc hx hy lt)))
    ((ZRLe _ _ le) (ZRLe a b (zmul-le-reg-r a b c x y hc hx hy le)))))

(def-fns _ $ (erased zr-add-reg-r : (erased (ORel) k) (erased (Z) a b c x y)
    (erased (ZAdd a c x) hx) (erased (ZAdd b c y) hy) (erased (ZR k x y) h) -> (erased (ZR k a b) r))
  (match erased h _
    ((ZRLt _ _ lt) (ZRLt a b (zadd-lt-reg-r a b c x y hx hy lt)))
    ((ZRLe _ _ le) (ZRLe a b (zadd-le-reg-r a b c x y hx hy le)))))

(def-fns _ $ (erased zr-add-mono : (erased (ORel) k1 k2 k) (erased (Z) a b c d x y) (erased (OMeet k1 k2 k) m) (erased (ZR k1 a b) h) (erased (ZR k2 c d) g)
    (erased (ZAdd a c x) hx) (erased (ZAdd b d y) hy) -> (erased (ZR k x y) r))
  (match erased m _
    ((OMeetLt _)
      (let-match erased h (ZRLt _ _ lt))
      (ZRLt x y (zadd-lt-le-mono a b c d x y lt (zr-le k2 c d g) hx hy)))
    ((OMeetLe _)
      (let-match erased h (ZRLe _ _ le))
      (match erased g _
        ((ZRLt _ _ lt) (ZRLt x y (zadd-le-lt-mono a b c d x y le lt hx hy)))
        ((ZRLe _ _ le2) (ZRLe x y (zadd-le-mono a b c d x y le le2 hx hy)))))))

(def-fns _ $ (erased zr-trans : (erased (ORel) k1 k2 k) (erased (Z) a b c) (erased (OMeet k1 k2 k) m) (erased (ZR k1 a b) h) (erased (ZR k2 b c) g)
    -> (erased (ZR k a c) r))
  (match erased m _
    ((OMeetLt _) (let-match erased h (ZRLt _ _ lt)) (ZRLt a c (zlt-le-trans a b c lt (zr-le k2 b c g))))
    ((OMeetLe _)
      (let-match erased h (ZRLe _ _ le))
      (match erased g _
        ((ZRLt _ _ lt) (ZRLt a c (zle-lt-trans a b c le lt)))
        ((ZRLe _ _ le2) (ZRLe a c (zle-trans a b c le le2)))))))

(def-fns _ $ (erased zring-r : (erased (ORel) k) (erased (List (Z)) env) (erased (ZExpr) p q s t) (erased (Z) zp zq zs zt)
    (erased (ZRingEq (ZEAdd p s) (ZEAdd q t)) h) (erased (ZEval env p zp) ep) (erased (ZEval env q zq) eq)
    (erased (ZEval env s zs) es) (erased (ZEval env t zt) et) (erased (ZR k zs zt) r) -> (erased (ZR k zq zp) g))
  (let ((erased x) (erased hp) (erased hq)) (zring-sums env p q s t zp zq zs zt h ep eq es et))
  (let ((erased u) (erased hu)) (zadd zq zs))
  (zr-add-reg-r k zq zp zs u x hu hp (zr-add-mono (OLe) k k zq zq zs zt u x (OMeetLe k) (ZRLe _ _ (zle-refl zq)) r hu hq)))
