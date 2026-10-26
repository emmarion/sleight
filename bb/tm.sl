(def-adts $ (Dir : -> Type)
  enum
  (many DL : -> (Dir))
  (many DR : -> (Dir)))

(def-adts $ (Tr : -> Type)
  enum
  (many Halt : -> (Tr))
  (many Go : (many (Bool) w) (many (Dir) d) (many (Nat) q) -> (Tr)))

(def-adts $ (Cfg : -> Type)
  enum
  (many MkCfg : (many (Nat) q) (many (List (Bool)) l) (many (Bool) h) (many (List (Bool)) r) -> (Cfg)))

(def-adts
  ((Look : ((List (Tr)) m) ((Nat) q) ((Bool) b) ((Tr) t) -> Type)
    enum
    (many Look0 : (erased (Tr) t0 t1) (erased (List (Tr)) rest) -> (Look (Cons (Tr) t0 (Cons (Tr) t1 rest)) (Zero) (BFalse) t0))
    (many Look1 : (erased (Tr) t0 t1) (erased (List (Tr)) rest) -> (Look (Cons (Tr) t0 (Cons (Tr) t1 rest)) (Zero) (BTrue) t1))
    (many LookS : (erased (Tr) t0 t1) (erased (List (Tr)) rest) (erased (Nat) q) (erased (Bool) b) (erased (Tr) t)
       (erased (Look rest q b t) p) -> (Look (Cons (Tr) t0 (Cons (Tr) t1 rest)) (Succ q) b t))))

(def-adts
  ((Pop : ((List (Bool)) xs) ((Bool) b) ((List (Bool)) ys) -> Type)
    enum
    (many PopNil : -> (Pop (Nil (Bool)) (BFalse) (Nil (Bool))))
    (many PopCons : (erased (Bool) b) (erased (List (Bool)) ys) -> (Pop (Cons (Bool) b ys) b ys))))

(def-adts
  ((Step : ((List (Tr)) m) ((Cfg) c) ((Cfg) d) -> Type)
    enum
    (many StepL : (erased (List (Tr)) m) (erased (Nat) q q2) (erased (List (Bool)) l r l2) (erased (Bool) h w h2)
       (erased (Look m q h (Go w (DL) q2)) lk) (erased (Pop l h2 l2) pp)
       -> (Step m (MkCfg q l h r) (MkCfg q2 l2 h2 (Cons (Bool) w r))))
    (many StepR : (erased (List (Tr)) m) (erased (Nat) q q2) (erased (List (Bool)) l r r2) (erased (Bool) h w h2)
       (erased (Look m q h (Go w (DR) q2)) lk) (erased (Pop r h2 r2) pp)
       -> (Step m (MkCfg q l h r) (MkCfg q2 (Cons (Bool) w l) h2 r2)))))

(def-adts
  ((HaltsIn : ((List (Tr)) m) ((Cfg) c) ((Nat) s) -> Type)
    enum
    (many HStop : (erased (List (Tr)) m) (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h)
       (erased (Look m q h (Halt)) lk) -> (HaltsIn m (MkCfg q l h r) (Succ (Zero))))
    (many HMove : (erased (List (Tr)) m) (erased (Cfg) c d) (erased (Nat) s)
       (erased (Step m c d) st) (erased (HaltsIn m d s) rest) -> (HaltsIn m c (Succ s)))))

(def-adts
  ((TrOK : ((Nat) n) ((Tr) t) -> Type)
    enum
    (many OKHalt : (erased (Nat) n) -> (TrOK n (Halt)))
    (many OKGo : (erased (Nat) n q) (erased (Bool) w) (erased (Dir) d) (erased (Lt q n) p) -> (TrOK n (Go w d q)))))

(def-adts
  ((Rows : ((Nat) n) ((Nat) k) ((List (Tr)) m) -> Type)
    enum
    (many RowsZ : (erased (Nat) n) -> (Rows n (Zero) (Nil (Tr))))
    (many RowsS : (erased (Nat) n k) (erased (Tr) t0 t1) (erased (List (Tr)) rest)
       (erased (TrOK n t0) o0) (erased (TrOK n t1) o1) (erased (Rows n k rest) p)
       -> (Rows n (Succ k) (Cons (Tr) t0 (Cons (Tr) t1 rest))))))

(def-adts $ (BBIs : ((Nat) n) ((Nat) k) -> Type)
  enum
  (many MkBB : (erased (Nat) n k) (erased (List (Tr)) champ) (erased (Rows n n champ) cw)
     (erased (HaltsIn champ (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) k) ch)
     (erased (Level) lv)
     (erased (Fn lv (erased (List (Tr)) m) (erased (Rows n n m) w) (erased (Nat) s)
                 (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) hm) ->
                 (erased (Lt s (Succ k)) p)) bound)
     -> (BBIs n k)))

(def-fns _ $ (erased look-fn : (erased (List (Tr)) m) (erased (Nat) q) (erased (Bool) b) (erased (Tr) t u)
    (subterm erased (Look m q b t) p) (erased (Look m q b u) p2) -> (erased (Eq (Tr) t u) e))
  (match erased p _
    ((Look0 t0 t1 rest) (let-match erased p2 (Look0 _ _ _)) (Refl (Tr) t))
    ((Look1 t0 t1 rest) (let-match erased p2 (Look1 _ _ _)) (Refl (Tr) t))
    ((LookS t0 t1 rest q1 b1 t1x p1)
      (let-match erased p2 (LookS _ _ _ _ _ u1 p21))
      (look-fn rest q1 b t u p1 p21))))

(def-fns _ $ (erased pop-fn : (erased (List (Bool)) xs ys zs) (erased (Bool) b c)
    (erased (Pop xs b ys) p) (erased (Pop xs c zs) p2) -> (erased (Eq (Bool) b c) e) (erased (Eq (List (Bool)) ys zs) f))
  (match erased p _
    ((PopNil) (let-match erased p2 (PopNil)) (values (Refl (Bool) b) (Refl (List (Bool)) ys)))
    ((PopCons b1 ys1) (let-match erased p2 (PopCons _ _)) (values (Refl (Bool) b) (Refl (List (Bool)) ys)))))

(def-fns _ $ (erased step-fn : (erased (List (Tr)) m) (erased (Cfg) c d e)
    (erased (Step m c d) p) (erased (Step m c e) p2) -> (erased (Eq (Cfg) d e) eq))
  (match erased p _
    ((StepL m1 q q2 l r l2 h w h2 lk pp)
      (match erased p2 _
        ((StepL _ _ q3 _ _ l3 _ w3 h3 lk3 pp3)
          (let-match erased (look-fn m q h _ _ lk lk3) (Refl _ _))
          (let ((erased e1) (erased e2)) (pop-fn l l2 l3 h2 h3 pp pp3))
          (let-match erased e1 (Refl _ _))
          (let-match erased e2 (Refl _ _))
          (Refl (Cfg) d))
        (absurd (StepR _ _ q3 _ _ r3 _ w3 h3 lk3 pp3) (look-fn m q h _ _ lk lk3))))
    ((StepR m1 q q2 l r r2 h w h2 lk pp)
      (match erased p2 _
        (absurd (StepL _ _ q3 _ _ l3 _ w3 h3 lk3 pp3) (look-fn m q h _ _ lk lk3))
        ((StepR _ _ q3 _ _ r3 _ w3 h3 lk3 pp3)
          (let-match erased (look-fn m q h _ _ lk lk3) (Refl _ _))
          (let ((erased e1) (erased e2)) (pop-fn r r2 r3 h2 h3 pp pp3))
          (let-match erased e1 (Refl _ _))
          (let-match erased e2 (Refl _ _))
          (Refl (Cfg) d))))))

(def-fns _ $ (erased halts-fn : (erased (List (Tr)) m) (erased (Cfg) c) (erased (Nat) s t)
    (subterm erased (HaltsIn m c s) p) (erased (HaltsIn m c t) p2) -> (erased (Eq (Nat) s t) e))
  (match erased p _
    ((HStop m1 q l r h lk)
      (match erased p2 _
        ((HStop _ _ _ _ _ lk2) (Refl (Nat) s))
        ((HMove _ _ d2 t1 st2 rest2)
          (match erased st2 _
            (absurd (StepL _ _ _ _ _ _ _ _ _ lk2 _) (look-fn m q h _ _ lk lk2))
            (absurd (StepR _ _ _ _ _ _ _ _ _ lk2 _) (look-fn m q h _ _ lk lk2))))))
    ((HMove m1 c1 d s1 st rest)
      (match erased p2 _
        ((HStop _ q l r h lk2)
          (match erased st _
            (absurd (StepL _ _ _ _ _ _ _ _ _ lk _) (look-fn m q h _ _ lk lk2))
            (absurd (StepR _ _ _ _ _ _ _ _ _ lk _) (look-fn m q h _ _ lk lk2))))
        ((HMove _ _ d2 t1 st2 rest2)
          (let-match erased (step-fn m c d d2 st st2) (Refl _ _))
          (eq-cong-succ s1 t1 (halts-fn m d s1 t1 rest rest2)))))))

(def-adts
  ((Mem : (Type A) (A x) ((List A) xs) -> Type)
    enum
    (many MemHere : (erased Type A) (erased A x) (erased (List A) rest) -> (Mem A x (Cons A x rest)))
    (many MemThere : (erased Type A) (erased A x y) (erased (List A) rest) (erased (Mem A x rest) p)
       -> (Mem A x (Cons A y rest)))))

(def-adts $ (Res : (Type P) -> Type)
  enum
  (many ROk : (erased Type P) (erased P p) -> (Res P))
  (many RFail : (erased Type P) -> (Res P)))

(def-adts
  ((SimR : ((List (Tr)) m) ((Cfg) c) -> Type)
    enum
    (many SHalt : (erased (List (Tr)) m) (erased (Cfg) c) (many (Nat) s) (erased (HaltsIn m c s) p) -> (SimR m c))
    (many SRun : (erased (List (Tr)) m) (erased (Cfg) c) -> (SimR m c))))

(def-fns _ $ (many eq-bit : (many (Bool) x) (many (Bool) y) -> (many (Maybe (Eq (Bool) x y)) r))
  (match many x _
    ((BFalse) (match many y _ ((BFalse) (Some _ (Refl (Bool) x))) ((BTrue) (None _))))
    ((BTrue) (match many y _ ((BTrue) (Some _ (Refl (Bool) x))) ((BFalse) (None _))))))

(def-fns _ $ (many eq-nat : (many (Nat) x) (many (Nat) y) -> (many (Maybe (Eq (Nat) x y)) r))
  (match many (nat-eq x y) _
    ((Equal _ _ _) (Some _ (Refl (Nat) x)))
    (else (None _))))

(def-adts
  ((Or : (Type P) (Type Q) -> Type)
    enum
    (many InL : (erased Type P Q) (erased P p) -> (Or P Q))
    (many InR : (erased Type P Q) (erased Q q) -> (Or P Q))))

(def-fns _ $ (erased lt-succ-cases : (erased (Nat) q n) (subterm erased (Lt q (Succ n)) lt) -> (erased (Or (Eq (Nat) q n) (Lt q n)) r))
  (match erased lt _
    ((LtZ _)
      (match erased n _
        ((Zero) (InL _ _ (Refl (Nat) q)))
        ((Succ n1) (InR _ _ (LtZ n1)))))
    ((LtS a _ p)
      (match erased n _
        (absurd (Zero) p)
        ((Succ n1)
          (match erased (lt-succ-cases a n1 p) _
            ((InL _ _ e) (let-match erased e (Refl _ _)) (InL _ _ (Refl (Nat) q)))
            ((InR _ _ l) (InR _ _ (LtS a n1 l)))))))))

(def-adts
  ((Range : ((Nat) n) ((List (Nat)) xs) -> Type)
    enum
    (many RgZ : -> (Range (Zero) (Nil (Nat))))
    (many RgS : (erased (Nat) n) (erased (List (Nat)) xs) (erased (Range n xs) p) -> (Range (Succ n) (Cons (Nat) n xs)))))

(def-fns _ $ (many range : (subterm many (Nat) n) -> (many (List (Nat)) xs) (erased (Range n xs) p))
  (let-match many n (Succ n1) ((Zero) (values (Nil (Nat)) (RgZ))))
  (let ((many xs) (erased p)) (notail $ range n1))
  (values (Cons (Nat) n1 xs) (RgS n1 xs p)))

(def-fns _ $ (erased range-mem : (erased (Nat) n q) (erased (List (Nat)) xs) (subterm erased (Range n xs) p) (erased (Lt q n) lt) ->
    (erased (Mem (Nat) q xs) mm))
  (match erased p _
    (absurd (RgZ) lt)
    ((RgS n1 xs1 p1)
      (match erased (lt-succ-cases q n1 lt) _
        ((InL _ _ e) (let-match erased e (Refl _ _)) (MemHere (Nat) q xs1))
        ((InR _ _ l) (MemThere (Nat) q n1 xs1 (range-mem n1 q xs1 p1 l)))))))

(def-adts
  ((Opts : ((List (Nat)) xs) ((List (Tr)) os) -> Type)
    enum
    (many OptsZ : -> (Opts (Nil (Nat)) (Cons (Tr) (Halt) (Nil (Tr)))))
    (many OptsS : (erased (Nat) q) (erased (List (Nat)) xs) (erased (List (Tr)) os) (erased (Opts xs os) p)
       -> (Opts (Cons (Nat) q xs) (Cons (Tr) (Go (BFalse) (DL) q) $ Cons (Tr) (Go (BFalse) (DR) q) $
                                   Cons (Tr) (Go (BTrue) (DL) q) $ Cons (Tr) (Go (BTrue) (DR) q) os)))))

(def-fns _ $ (many opts : (subterm many (List (Nat)) xs) -> (many (List (Tr)) os) (erased (Opts xs os) p))
  (let-match many xs (Cons _ q rest) ((Nil _) (values (Cons (Tr) (Halt) (Nil (Tr))) (OptsZ))))
  (let ((many os) (erased p)) (notail $ opts rest))
  (values (Cons (Tr) (Go (BFalse) (DL) q) $ Cons (Tr) (Go (BFalse) (DR) q) $ Cons (Tr) (Go (BTrue) (DL) q) $ Cons (Tr) (Go (BTrue) (DR) q) os)
          (OptsS q rest os p)))

(def-fns _ $ (erased mem-skip4 : (erased (Tr) t a b c d) (erased (List (Tr)) os) (erased (Mem (Tr) t os) mm) ->
    (erased (Mem (Tr) t (Cons (Tr) a $ Cons (Tr) b $ Cons (Tr) c $ Cons (Tr) d os)) r))
  (MemThere _ t a _ $ MemThere _ t b _ $ MemThere _ t c _ $ MemThere _ t d _ mm))

(def-fns _ $ (erased opts-halt : (erased (List (Nat)) xs) (erased (List (Tr)) os) (subterm erased (Opts xs os) p) ->
    (erased (Mem (Tr) (Halt) os) mm))
  (match erased p _
    ((OptsZ) (MemHere (Tr) (Halt) (Nil (Tr))))
    ((OptsS q xs1 os1 p1) (mem-skip4 (Halt) _ _ _ _ os1 (opts-halt xs1 os1 p1)))))

(def-fns _ $ (erased opts-go : (erased (List (Nat)) xs) (erased (List (Tr)) os) (erased (Nat) q) (erased (Bool) w) (erased (Dir) d)
    (subterm erased (Opts xs os) p) (erased (Mem (Nat) q xs) mq) -> (erased (Mem (Tr) (Go w d q) os) mm))
  (match erased p _
    (absurd (OptsZ) mq)
    ((OptsS q1 xs1 os1 p1)
      (match erased mq _
        ((MemHere _ _ _)
          (match erased w _
            ((BFalse)
              (match erased d _
                ((DL) (MemHere (Tr) (Go w d q) _))
                ((DR) (MemThere _ _ _ _ (MemHere (Tr) (Go w d q) _)))))
            ((BTrue)
              (match erased d _
                ((DL) (MemThere _ _ _ _ $ MemThere _ _ _ _ (MemHere (Tr) (Go w d q) _)))
                ((DR) (MemThere _ _ _ _ $ MemThere _ _ _ _ $ MemThere _ _ _ _ (MemHere (Tr) (Go w d q) _)))))))
        ((MemThere _ _ _ _ mq1) (mem-skip4 (Go w d q) _ _ _ _ os1 (opts-go xs1 os1 q w d p1 mq1)))))))

(def-fns _ $ (erased tr-mem : (erased (Nat) n) (erased (List (Nat)) xs) (erased (List (Tr)) os) (erased (Tr) t)
    (erased (TrOK n t) ok) (erased (Range n xs) rg) (erased (Opts xs os) op) -> (erased (Mem (Tr) t os) mm))
  (match erased ok _
    ((OKHalt _) (opts-halt xs os op))
    ((OKGo _ q w d lt) (opts-go xs os q w d op (range-mem n q xs rg lt)))))
