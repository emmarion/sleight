(def-adts
  ((MirT : ((Tr) t) ((Tr) u) -> Type)
    enum
    (many MTH : -> (MirT (Halt) (Halt)))
    (many MTL : (erased (Bool) w) (erased (Nat) q) -> (MirT (Go w (DL) q) (Go w (DR) q)))
    (many MTR : (erased (Bool) w) (erased (Nat) q) -> (MirT (Go w (DR) q) (Go w (DL) q)))))

(def-adts
  ((MirM : ((List (Tr)) m) ((List (Tr)) v) -> Type)
    enum
    (many MMNil : -> (MirM (Nil (Tr)) (Nil (Tr))))
    (many MMCons : (erased (Tr) t u) (erased (List (Tr)) m v) (erased (MirT t u) e) (erased (MirM m v) mv)
       -> (MirM (Cons (Tr) t m) (Cons (Tr) u v)))))

(def-fns _ $ (erased mir-t : (erased (Tr) t) -> (erased (Tr) u) (erased (MirT t u) e))
  (let-match erased t (Go w d q) ((Halt) (values (Halt) (MTH))))
  (match erased d _ ((DL) (values (Go w (DR) q) (MTL w q))) ((DR) (values (Go w (DL) q) (MTR w q)))))

(def-fns _ $ (erased mir-m : (subterm erased (List (Tr)) m) -> (erased (List (Tr)) v) (erased (MirM m v) mv))
  (let-match erased m (Cons _ t rest) ((Nil _) (values (Nil (Tr)) (MMNil))))
  (let ((erased u) (erased e)) (mir-t t))
  (let ((erased v1) (erased mv1)) (mir-m rest))
  (values (Cons (Tr) u v1) (MMCons t u rest v1 e mv1)))

(def-fns _ $ (erased mir-ok : (erased (Nat) n) (erased (Tr) t u) (erased (TrOK n t) o) (erased (MirT t u) e) -> (erased (TrOK n u) o2))
  (match erased e _
    ((MTH) (OKHalt n))
    ((MTL w q) (let-match erased o (OKGo _ _ _ _ lt)) (OKGo n q w (DR) lt))
    ((MTR w q) (let-match erased o (OKGo _ _ _ _ lt)) (OKGo n q w (DL) lt))))

(def-fns _ $ (erased mir-rows : (erased (Nat) n k) (erased (List (Tr)) m v) (subterm erased (Rows n k m) w) (erased (MirM m v) mv)
    -> (erased (Rows n k v) res))
  (match erased w _
    ((RowsZ _) (let-match erased mv (MMNil)) (RowsZ n))
    ((RowsS _ k1 t0 t1 rest o0 o1 w1)
      (let-match erased mv (MMCons _ u0 _ _ e0 mv1))
      (let-match erased mv1 (MMCons _ u1 _ v1 e1 mv2))
      (RowsS n k1 u0 u1 v1 (mir-ok n t0 u0 o0 e0) (mir-ok n t1 u1 o1 e1) (mir-rows n k1 rest v1 w1 mv2)))))

(def-fns _ $ (erased mir-look : (erased (List (Tr)) m v) (erased (Nat) q) (erased (Bool) b) (erased (Tr) t)
    (subterm erased (Look m q b t) lk) (erased (MirM m v) mv) -> (erased (Tr) u) (erased (MirT t u) e) (erased (Look v q b u) lk2))
  (match erased lk _
    ((Look0 t0 t1 rest)
      (let-match erased mv (MMCons _ u0 _ _ e0 mv1))
      (let-match erased mv1 (MMCons _ u1 _ v1 _ _))
      (values u0 e0 (Look0 u0 u1 v1)))
    ((Look1 t0 t1 rest)
      (let-match erased mv (MMCons _ u0 _ _ _ mv1))
      (let-match erased mv1 (MMCons _ u1 _ v1 e1 _))
      (values u1 e1 (Look1 u0 u1 v1)))
    ((LookS t0 t1 rest q1 _ _ lk1)
      (let-match erased mv (MMCons _ u0 _ _ _ mv1))
      (let-match erased mv1 (MMCons _ u1 _ v1 _ mv2))
      (let ((erased u) (erased e) (erased lk2)) (mir-look rest v1 q1 b t lk1 mv2))
      (values u e (LookS u0 u1 v1 q1 b u lk2)))))

(def-fns _ $ (erased mir-halts : (erased (List (Tr)) m v) (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h) (erased (Nat) s)
    (subterm erased (HaltsIn m (MkCfg q l h r) s) hs) (erased (MirM m v) mv) -> (erased (HaltsIn v (MkCfg q r h l) s) res))
  (match erased hs _
    ((HStop _ _ _ _ _ lk)
      (let ((erased u) (erased e) (erased lk2)) (mir-look m v q h (Halt) lk mv))
      (let-match erased e (MTH))
      (HStop v q r l h lk2))
    ((HMove _ _ _ s1 st rest)
      (match erased st _
        ((StepL _ _ q2 _ _ l2 _ w h2 lk pp)
          (let ((erased u) (erased e) (erased lk2)) (mir-look m v q h (Go w (DL) q2) lk mv))
          (let-match erased e (MTL _ _))
          (HMove v _ _ s1 (StepR v q q2 r l l2 h w h2 lk2 pp) (mir-halts m v q2 l2 (Cons (Bool) w r) h2 s1 rest mv)))
        ((StepR _ _ q2 _ _ r2 _ w h2 lk pp)
          (let ((erased u) (erased e) (erased lk2)) (mir-look m v q h (Go w (DR) q2) lk mv))
          (let-match erased e (MTR _ _))
          (HMove v _ _ s1 (StepL v q q2 r l r2 h w h2 lk2 pp) (mir-halts m v q2 (Cons (Bool) w l) r2 h2 s1 rest mv)))))))

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

(def-fns _ $ (erased orient : (erased (Nat) n) (erased (List (Tr)) m) (erased (Nat) s) (erased (Rows n n m) w)
    (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h) ->
    (erased (List (Tr)) m2) (erased (Rows n n m2) w2) (erased (Tr) t) (erased (Look m2 (Zero) (BFalse) t) lk) (erased (NotL t) nl)
    (erased (HaltsIn m2 (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h2))
  (let-match erased w (RowsS _ _ t0 t1 rest _ _ _)
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
  (let ((erased v) (erased mv)) (mir-m m))
  (let ((erased u) (erased e) (erased lk2)) (mir-look m v (Zero) (BFalse) t0 lk0 mv))
  (let-match erased e (MTL _ _))
  (values v (mir-rows n n m v w mv) u lk2 (NLR w0 q) (mir-halts m v (Zero) (Nil (Bool)) (Nil (Bool)) (BFalse) s h mv)))

(def-fns _ $ (erased sym-good : (erased (Nat) n k) (erased (List (Nat)) xs) (erased (List (Tr)) O OR) (erased (List (PT)) p0)
    (erased (TAll k O p0 (Zero) (BFalse) OR) ta) (erased (UList n p0) up) (erased (KeepR O OR) kr) (erased (Range n xs) rg)
    (erased (Opts xs O) op) (erased (List (Tr)) m) (erased (Nat) s) (erased (Rows n n m) w)
    (erased (HaltsIn m (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) s) h) -> (erased (Lt s (Succ k)) res))
  (let ((erased m2) (erased w2) (erased t) (erased lk) (erased nl) (erased h2)) (orient n m s w h))
  (let-match erased up (UCons _ p1 _) (absurd (UNil) (let-match erased w2 (RowsZ _)) lk))
  (let ((erased mm)) (keep-mem t O OR kr (tr-mem n xs O t (look-ok n n (Zero) m2 (BFalse) t w2 lk) rg op) nl))
  (ta-pick n k xs O p0 m2 s (Zero) (BFalse) t OR ta mm (ext-undef n n m2 p0 w2 up) (PL0 (Undef) (Undef) p1) lk w2 rg op h2))
