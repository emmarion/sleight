(def-fns _ $ (many monus : (many (Nat) a b) -> (many (Nat) c))
  (let-match many (lt-dec b (Succ a)) (Yes _ _ _ _ le) ((No _ _ _ _ _) (Zero)))
  (let ((many c) (erased _)) (sub a b le))
  c)

(def-fns _ $ (many nrev : (many (List (Nat)) A) (subterm many (List (Nat)) D) -> (many (List (Nat)) R))
  (let-match many D (Cons _ d D1) ((Nil _) A))
  (tail $ nrev (Cons _ d A) D1))

(def-fns _ $ (many nlen : (subterm many (List (Nat)) D) -> (many (Nat) n))
  (let-match many D (Cons _ _ D1) ((Nil _) (Zero)))
  (Succ (notail $ nlen D1)))

(def-fns _ $ (many lo3 : (many (Nat) l) (many (Ps) x0) (many (Ps) x1) (many (Ps) x2) -> (many (Maybe (Ps)) x))
  (let-match many l (Succ l1) ((Zero) (Some _ x0)))
  (let-match many l1 (Succ l2) ((Zero) (Some _ x1)))
  (let-match many l2 (Zero) ((Succ _) (None _)))
  (Some _ x2))

(def-fns _ $ (many pair-of : (many (Nat) h) (many (Nat) l) -> (many (Maybe (Ps)) x))
  (let-match many h (Succ h1) ((Zero) (lo3 l (PrC) (PrD) (PrDp))))
  (let-match many h1 (Zero) ((Succ _) (None _)))
  (lo3 l (PrA) (PrB) (PrBp)))

(def-fns _ $ (many pairs : (subterm many (List (Nat)) D) -> (many (Maybe (List (Ps))) w))
  (let-match many D (Cons _ a D1) ((Nil _) (Some _ (Nil (Ps)))))
  (let-match many D1 (Cons _ b D2) ((Nil _) (None _)))
  (let-match many (pair-of a b) (Some _ x) ((None _) (None _)))
  (let-match many (notail $ pairs D2) (Some _ w) ((None _) (None _)))
  (Some _ (Cons _ x w)))

(def-adts $ (Vl : -> Type)
  enum
  (many MkVl : (many (Nat) v) (many (Nat) k) -> (Vl)))

(def-fns _ $ (many vl-pass : (subterm many (List (Vl)) V) -> (many (List (Vl)) W))
  (let-match many V (Cons _ a V1) ((Nil _) V))
  (let-match many V1 (Cons _ b V2) ((Nil _) V))
  (let-match many a (MkVl va ka))
  (let-match many b (MkVl vb kb))
  (Cons _ (MkVl (nat-add (nat-shl va (nat-add kb kb)) vb) (nat-add ka kb)) (notail $ vl-pass V2)))

(def-fns _ $ (many vl-loop : (subterm many (Nat) fuel) (many (List (Vl)) V) -> (many (Nat) v))
  (let-match many V (Cons _ a V1) ((Nil _) (Zero)))
  (let-match many a (MkVl va _))
  (let-match many V1 (Cons _ _ _) ((Nil _) va))
  (let-match many fuel (Succ f) ((Zero) (Zero)))
  (tail $ vl-loop f (vl-pass V)))

(def-adts $ (Rho : -> Type)
  enum
  (many MkRho : (many (Nat) r) (many (Nat) m) -> (Rho))
  (many RhoNo : -> (Rho)))

(def-fns _ $ (many ps-d : (many (Ps) x) -> (many (Nat) d))
  (match many x _ ((PrDp) 0) ((PrD) 0) ((PrC) 1) ((PrBp) 2) ((PrB) 2) ((PrA) 3)))

(def-fns _ $ (many ps-c : (many (Ps) x) -> (many (Nat) c))
  (match many x _ ((PrDp) 0) ((PrD) 1) ((PrC) 1) ((PrBp) 1) ((PrB) 2) ((PrA) 2)))

(def-fns _ $ (many vrev : (subterm many (List (Vl)) V) (many (List (Vl)) acc) -> (many (List (Vl)) W))
  (let-match many V (Cons _ a V1) ((Nil _) acc))
  (tail $ vrev V1 (Cons _ a acc)))

(def-fns _ $ (many g4 : (many (Nat) k) -> (many (Nat) g))
  (let ((many q) (erased _) (erased _) (erased _) (erased _) (erased _)) (div (monus (nat-shl 1 (nat-add k k)) 1) (Succ (Succ (Succ (Zero)))) (LtZ _)))
  q)

(def-fns _ $ (many rho-fin : (many (List (Vl)) cs) (many (Nat) S C a m) -> (many (Rho) r))
  (let ((many v)) (vl-loop 100 (vrev cs (Nil (Vl)))))
  (let ((many e)) (Succ (monus m a)))
  (let ((many q) (erased _) (erased _) (erased _) (erased _) (erased _)) (div (monus (nat-shl v (nat-add e e)) S) (Succ (Succ (Succ (Zero)))) (LtZ _)))
  (MkRho (nat-add q C) m))

(def-fns _ $ (many rho-b : (subterm many (List (Nat)) Q) (many (List (Vl)) cs) (many (Nat) S C a m) -> (many (Rho) r))
  (let-match many Q (Cons _ h Q1) ((Nil _) (rho-fin cs S C a m)))
  (let-match many Q1 (Cons _ l Q2) ((Nil _) (RhoNo)))
  (let-match many (pair-of h l) (Some _ _) ((None _) (RhoNo)))
  (tail $ rho-b Q2 cs S C a (Succ m)))

(def-fns _ $ (many rho-a : (subterm many (List (Nat)) Q) (many (Nat) v k) (many (List (Vl)) cs) (many (Nat) S C a) -> (many (Rho) r))
  (let-match many Q (Cons _ h Q1) ((Nil _) (rho-fin (Cons _ (MkVl v k) cs) S C a a)))
  (let-match many Q1 (Cons _ l w1) ((Nil _) (RhoNo)))
  (let-match many (pair-of h l) (Some _ x) ((None _) (RhoNo)))
  (let ((many d)) (ps-d x))
  (let ((many v1)) (nat-add (nat-add v v) (nat-add v v)))
  (let ((many v2)) (nat-add v1 d))
  (let ((many S1)) (nat-add S d))
  (let ((many C1)) (nat-add C (ps-c x)))
  (let ((many a1)) (Succ a))
  (match many x _
    ((PrDp) (rho-b w1 (Cons _ (MkVl v2 (Succ k)) cs) S1 C1 a1 a1))
    ((PrBp) (rho-b w1 (Cons _ (MkVl v2 (Succ k)) cs) S1 C1 a1 a1))
    (else (match many (nat-eq k 30) _
      ((Equal _ _ _) (tail $ rho-a w1 0 0 (Cons _ (MkVl v2 31) cs) S1 C1 a1))
      (else (tail $ rho-a w1 v2 (Succ k) cs S1 C1 a1))))))

(def-fns _ $ (many rho-q : (many (List (Nat)) Q) -> (many (Rho) r))
  (rho-a Q 0 0 (Nil (Vl)) 0 0 0))

(def-fns _ $ (many ps-digits : (subterm many (List (Ps)) w) -> (many (List (Nat)) Q))
  (let-match many w (Cons _ x w1) ((Nil _) (Nil (Nat))))
  (let ((many Q1)) (notail $ ps-digits w1))
  (match many x _
    ((PrA) (Cons _ 1 (Cons _ 0 Q1))) ((PrB) (Cons _ 1 (Cons _ 1 Q1))) ((PrBp) (Cons _ 1 (Cons _ 2 Q1)))
    ((PrC) (Cons _ 0 (Cons _ 0 Q1))) ((PrD) (Cons _ 0 (Cons _ 1 Q1))) ((PrDp) (Cons _ 0 (Cons _ 2 Q1)))))

(def-fns _ $ (many odd-s : (many (Nat) h) (many (Rho) rho) -> (many (Nat) s))
  (let-match many rho (MkRho r m) ((RhoNo) (Zero)))
  (let-match many h (Succ h1) ((Zero) (Succ (nat-add r (g4 (Succ m))))))
  (let-match many h1 (Succ _) ((Zero) (Succ r)))
  (Zero))

(def-adts $ (Dec : -> Type)
  enum
  (many DecOk : (many (Fam) F) (many (Nat) s) -> (Dec))
  (many DecNo : -> (Dec)))

(def-fns _ $ (many tail-lo : (many (Tt) T) -> (many (Maybe (Nat)) lo))
  (match many T _
    ((Tt11) (Some _ (Zero)))
    ((Tt011) (Some _ (Succ (Zero))))
    ((Tt0011) (Some _ (Succ (Succ (Zero)))))
    (else (None _))))

(def-fns _ $ (many fam-of : (many (Bool) v2) (many (Bool) odd) (many (Nat) P) (many (Tt) T) -> (many (Fam) F))
  (match many v2 _
    ((BFalse) (match many odd _ ((BFalse) (FE P T)) ((BTrue) (FO P T))))
    ((BTrue) (match many odd _ ((BFalse) (FVE (Succ P))) ((BTrue) (FVO (Succ P)))))))

(def-adts $ (TDg : -> Type)
  enum
  (many TdOk : (many (List (Nat)) RD) (many (Nat) m) -> (TDg))
  (many TdNo : -> (TDg)))

(def-fns _ $ (many tdg : (many (Nat) acc) (subterm many (List (Tk)) X) (many (List (Nat)) RD) (many (Nat) m) -> (many (TDg) r))
  (let-match many X (Cons _ x X1) ((Nil _) (match many (nat-zero-dec acc) _ ((IsZero) (TdOk RD m)) ((IsSucc _) (TdNo)))))
  (match many x _
    ((Tp) (tail $ tdg (Succ acc) X1 RD m))
    ((T0) (let-match many (nat-zero-dec acc) (IsZero) ((IsSucc _) (TdNo))) (tail $ tdg 0 X1 (Cons _ 0 RD) (Succ m)))
    ((T1) (tail $ tdg 0 X1 (Cons _ (Succ acc) RD) (Succ m)))))

(def-fns _ $ (many dec-q : (many (Bool) v2) (many (Nat) m) (many (List (Nat)) RD1 E) (many (Tt) T) -> (many (Dec) r))
  (let-match many RD1 (Cons _ _ _) ((Nil _) (DecNo)))
  (let-match many (nrev E RD1) (Cons _ d0 Q) ((Nil _) (DecNo)))
  (let-match many (nat-eq d0 2) (Equal _ _ _) (else (DecNo)))
  (let ((many n) (many par) (erased _) (erased _) (erased _) (erased _)) (divmod (monus m 2) (Succ (Succ (Zero))) (LtZ _)))
  (let-match many par (Succ _) ((Zero)
    (let-match many (rho-q Q) (MkRho r _) ((RhoNo) (DecNo)))
    (DecOk (fam-of v2 (BFalse) n T) r)))
  (let-match many Q (Cons _ h Q1) ((Nil _) (DecNo)))
  (let ((many rho)) (rho-q Q1))
  (let-match many rho (MkRho _ _) ((RhoNo) (DecNo)))
  (DecOk (fam-of v2 (BTrue) n T) (odd-s h rho)))

(def-fns _ $ (many decode : (many (List (Tk)) X) (many (Tt) T) -> (many (Dec) r))
  (let-match many (tdg 0 X (Nil (Nat)) 0) (TdOk RD m) ((TdNo) (DecNo)))
  (let-match many RD (Cons _ last RD1) ((Nil _) (DecNo)))
  (let-match many (tail-lo T) (Some _ lo) ((None _)
    (let-match many (nat-zero-dec last) (IsZero) ((IsSucc _) (DecNo)))
    (dec-q (BFalse) m RD1 (Nil (Nat)) T)))
  (dec-q (BTrue) m RD1 (Cons _ last (Cons _ lo (Nil (Nat)))) T))
