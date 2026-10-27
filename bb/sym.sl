(def-adts
  ((NotL : ((Tr) t) -> Type)
    enum
    (many NLH : -> (NotL (Halt)))
    (many NLR : (erased (Bool) w) (erased (Nat) q) -> (NotL (Go w (DR) q)))))

(def-adts
  ((KeepR : ((List (Tr)) os) ((List (Tr)) ks) -> Type)
    enum
    (many KNil : -> (KeepR (Nil (Tr)) (Nil (Tr))))
    (many KDrop : (erased (Bool) w) (erased (Nat) q) (erased (List (Tr)) os ks) (erased (KeepR os ks) p)
       -> (KeepR (Cons (Tr) (Go w (DL) q) os) ks))
    (many KKeep : (erased (Tr) t) (erased (List (Tr)) os ks) (erased (NotL t) nl) (erased (KeepR os ks) p)
       -> (KeepR (Cons (Tr) t os) (Cons (Tr) t ks)))))

(def-fns _ $ (many keep-r : (subterm many (List (Tr)) os) -> (many (List (Tr)) ks) (erased (KeepR os ks) p))
  (let-match many os (Cons _ t rest) ((Nil _) (values (Nil (Tr)) (KNil))))
  (let ((many ks) (erased p)) (notail $ keep-r rest))
  (let-match many t (Go w d q) ((Halt) (values (Cons (Tr) t ks) (KKeep t rest ks (NLH) p))))
  (match many d _
    ((DL) (values ks (KDrop w q rest ks p)))
    ((DR) (values (Cons (Tr) t ks) (KKeep t rest ks (NLR w q) p)))))

(def-fns _ $ (erased keep-mem : (erased (Tr) t) (erased (List (Tr)) os ks) (subterm erased (KeepR os ks) kp) (erased (Mem (Tr) t os) mm)
    (erased (NotL t) nl) -> (erased (Mem (Tr) t ks) res))
  (match erased kp _
    ((KNil) (match erased mm _))
    ((KDrop w q os1 _ p1)
      (match erased mm _
        (absurd (MemHere _ _ _) nl)
        ((MemThere _ _ _ _ mm1) (keep-mem t os1 ks p1 mm1 nl))))
    ((KKeep t1 os1 ks1 _ p1)
      (match erased mm _
        ((MemHere _ _ _) (MemHere (Tr) t ks1))
        ((MemThere _ _ _ _ mm1) (MemThere (Tr) t t1 ks1 (keep-mem t os1 ks1 p1 mm1 nl)))))))

(def-fns _ $ (erased notl-xt : (erased (Nat) a b) (erased (Tr) t u) (erased (NotL t) nl) (erased (XT (BFalse) a b t u) e) -> (erased (NotL u) nl2))
  (let-match erased nl (NLR w q) ((NLH) (let-match erased e (XTH _ _ _)) (NLH)))
  (let-match erased e (XTG _ _ _ _ _ _ _ q2 fl _))
  (let-match erased fl (FlN _))
  (NLR w q2))

(def-fns _ $ (erased below-u : (erased (Nat) c k) (erased (List (PT)) p) (subterm erased (UList k p) u) -> (erased (Below c p) bl))
  (let-match erased u (UCons k1 p1 u1) ((UNil) (BlwNil c)))
  (BlwU c _ (BlwU c p1 (below-u c k1 p1 u1))))

(def-fns _ $ (erased orient : (erased (Nat) n) (erased (List (Tr)) m) (erased (Nat) s) (erased (Rows n n m) w)
    (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h) ->
    (erased (List (Tr)) m2) (erased (Rows n n m2) w2) (erased (Tr) t) (erased (Look m2 (Zero) (BFalse) t) lk) (erased (NotL t) nl)
    (erased (HaltsIn m2 (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h2))
  (let-match erased w (RowsS _ k1 t0 t1 rest _ _ _)
    (absurd (RowsZ _)
      (match erased h _
        (absurd (HStop _ _ _ _ _ lk) lk)
        (absurd (HMove _ _ _ _ st _)
          (match erased st _
            (absurd (StepL _ _ _ _ _ _ _ _ _ lk _) lk)
            (absurd (StepR _ _ _ _ _ _ _ _ _ lk _) lk))))))
  (let ((erased lk0)) (Look0 t0 t1 rest))
  (let-match erased t0 (Go w0 d q) ((Halt) (values m w (Halt) lk0 (NLH) h)))
  (let-match erased d (DL) ((DR) (values m w (Go w0 (DR) q) lk0 (NLR w0 q) h)))
  (let ((erased v) (erased x)) (xm-of (BTrue) (Zero) (Zero) m))
  (let ((erased pm)) (PMId (BTrue) (Zero) m v x))
  (let ((erased sz)) (SwA (Zero) (Zero)))
  (let ((erased u) (erased e) (erased lk2)) (pm-look (BTrue) (Zero) (Zero) m v (Zero) (Zero) (BFalse) t0 lk0 pm sz))
  (let-match erased e (XTG _ _ _ _ _ _ _ q2 fl _))
  (let-match erased fl (FlL))
  (values v (pm-rows n (BTrue) (Zero) (Zero) m v w pm (LtZ k1) (LtZ k1)) u lk2 (NLR w0 q2)
    (pm-halts (BTrue) (Zero) (Zero) m v (Zero) (Zero) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (Nil (Bool)) (BFalse) s h pm sz (FC1 (Nil (Bool)) (Nil (Bool))))))

(def-fns _ $ (erased sym-good : (erased (Nat) n k c2) (erased (List (Nat)) xs) (erased (List (Tr)) O OR) (erased (List (PT)) p0)
    (erased (TAll n k p0 (Zero) (BFalse) OR) ta) (erased (UList n p0) up) (erased (KeepR O OR) kr) (erased (Range c2 xs) rg)
    (erased (Opts xs O) op) (erased (NextC n (Succ (Zero)) c2) nc) (erased (List (Tr)) m) (erased (Nat) s) (erased (Rows n n m) w)
    (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h) -> (erased (Lt s (Succ k)) res))
  (let ((erased m2) (erased w2) (erased t) (erased lk) (erased nl) (erased h2)) (orient n m s w h))
  (let-match erased up (UCons k1 p1 u1) (absurd (UNil) (let-match erased w2 (RowsZ _)) lk))
  (let ((erased m3) (erased ex3) (erased w3) (erased h3) (erased t3) (erased lk3) (erased mm) (erased a) (erased b) (erased e))
    (fit n (Succ (Zero)) c2 (Zero) s xs O p0 m2 (BFalse) t rg op nc (UFS (Zero) (Undef) (Undef) p1 (UFZ k1 p1 u1))
      (below-u (Succ (Zero)) n p0 up) (LtZ (Zero)) (ext-undef n n m2 p0 w2 up) w2 h2 lk))
  (ta-pick n k p0 m3 s (Zero) (BFalse) t3 OR ta (keep-mem t3 O OR kr mm (notl-xt a b t t3 nl e)) ex3 (PL0 (Undef) (Undef) p1) lk3 w3 h3))
