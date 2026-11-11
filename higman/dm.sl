(def-adts $ (RLt : ((Nat) n) ((List (Nat)) a) ((List (Nat)) b) -> Type)
  enum
  (many MkRLt : (erased (Nat) n p) (erased (List (Nat)) a b) (erased (LexPos n p a b) l) -> (RLt n a b)))

(def-adts $ (RCmp : ((Nat) n) ((List (Nat)) a) ((List (Nat)) b) -> Type)
  enum
  (many RCLt : (erased (Nat) n) (erased (List (Nat)) a b) (many (Nat) p) (erased (LexPos n p a b) l) -> (RCmp n a b))
  (many RCEq : (erased (Nat) n) (erased (List (Nat)) a) -> (RCmp n a a))
  (many RCGt : (erased (Nat) n) (erased (List (Nat)) a b) (many (Nat) p) (erased (LexPos n p b a) l) -> (RCmp n a b)))

(def-fns _ $ (many rank-cmp : (erased (Nat) n) (subterm many (List (Nat)) a) (many (List (Nat)) b)
    (erased (Length (Nat) a n) la) (erased (Length (Nat) b n) lb) -> (many (RCmp n a b) c))
  (let-match many a (Cons _ x a1)
    ((Nil _) (let-match erased la (LengthNil _)) (let-match erased lb (LengthNil _)) (RCEq n a)))
  (let-match erased la (LengthCons _ _ _ n1 la1))
  (let-match erased lb (LengthCons _ y0 b0 _ lb1))
  (let-match many b (Cons _ y b1))
  (let-match many (nat-cmp x y) (CEq _ _ _)
    ((CLt _ _ _ _ l) (RCLt n a b (Zero) (LPHead n1 x y l a1 b1)))
    ((CGt _ _ _ _ l) (RCGt n a b (Zero) (LPHead n1 y x l b1 a1))))
  (match many (notail $ rank-cmp n1 a1 b1 la1 lb1) _
    ((RCLt _ _ _ p lp) (RCLt n a b (Succ p) (LPTail n1 p x a1 b1 lp)))
    ((RCEq _ _) (RCEq n a))
    ((RCGt _ _ _ p lp) (RCGt n a b (Succ p) (LPTail n1 p x b1 a1 lp)))))

(def-fns _ $ (erased absurd lexpos-irrefl : (erased (Nat) n p) (erased (List (Nat)) a) (subterm erased (LexPos n p a a) l)
    -> (erased (False) f))
  (match erased l _
    (absurd (LPHead _ h _ lt _ _) (lt-irrefl h lt))
    (absurd (LPTail n1 p1 _ t _ l1) (lexpos-irrefl n1 p1 t l1))))

(def-fns _ $ (erased lexpos-trans : (erased (Nat) n p q) (erased (List (Nat)) a b c) (subterm erased (LexPos n p a b) l1)
    (erased (LexPos n q b c) l2) -> (erased (Nat) s) (erased (LexPos n s a c) l))
  (match erased l1 _
    ((LPHead n1 h1 h2 lt t1 t2)
      (let-match erased l2 (LPTail _ _ _ _ t3 _)
        ((LPHead _ _ h3 lt2 _ t3) (values (Zero) (LPHead n1 h1 h3 (lt-trans h1 h2 h3 lt lt2) t1 t3))))
      (values (Zero) (LPHead n1 h1 h2 lt t1 t3)))
    ((LPTail n1 p1 h t1 t2 l3)
      (let-match erased l2 (LPTail _ q1 _ _ t3 l4) ((LPHead _ _ h3 lt2 _ t3) (values (Zero) (LPHead n1 h h3 lt2 t1 t3))))
      (let ((erased s1) (erased l5)) (lexpos-trans n1 p1 q1 t1 t2 t3 l3 l4))
      (values (Succ s1) (LPTail n1 s1 h t1 t3 l5)))))

(def-fns _ $ (erased rlt-trans : (erased (Nat) n) (erased (List (Nat)) a b c) (erased (RLt n a b) l1) (erased (RLt n b c) l2)
    -> (erased (RLt n a c) l))
  (let-match erased l1 (MkRLt _ p _ _ x1))
  (let-match erased l2 (MkRLt _ q _ _ x2))
  (let ((erased s) (erased x)) (lexpos-trans n p q a b c x1 x2))
  (MkRLt n s a c x))

(def-fns _ $ (erased absurd rlt-irrefl : (erased (Nat) n) (erased (List (Nat)) a) (erased (RLt n a a) l) -> (erased (False) f))
  (let-match erased l (MkRLt _ p _ _ x))
  (lexpos-irrefl n p a x))

(def-fns _ $ (erased absurd rlt-asym : (erased (Nat) n) (erased (List (Nat)) a b) (erased (RLt n a b) l1) (erased (RLt n b a) l2)
    -> (erased (False) f))
  (rlt-irrefl n a (rlt-trans n a b a l1 l2)))

(def-adts $ (Grp : -> Type)
  enum
  (many MkGrp : (many (List (Nat)) r) (many (Nat) c) -> (Grp)))

; Hd n r gs : the first group of gs, if any, has a rank below r.
(def-adts $ (Hd : ((Nat) n) ((List (Nat)) r) ((List (Grp)) gs) -> Type)
  enum
  (many HdNil : (erased (Nat) n) (erased (List (Nat)) r) -> (Hd n r (Nil (Grp))))
  (many HdCons : (erased (Nat) n) (erased (List (Nat)) r r2) (erased (Nat) c) (erased (List (Grp)) gs) (erased (RLt n r2 r) l)
     -> (Hd n r (Cons (Grp) (MkGrp r2 c) gs))))

(def-adts $ (Desc : ((Nat) n) ((List (Grp)) gs) -> Type)
  enum
  (many DcNil : (erased (Nat) n) -> (Desc n (Nil (Grp))))
  (many DcCons : (erased (Nat) n) (erased (List (Nat)) r) (erased (Nat) c) (erased (List (Grp)) gs) (erased (Length (Nat) r n) ln)
     (erased (Lt (Zero) c) pos) (erased (Hd n r gs) h) (erased (Desc n gs) d) -> (Desc n (Cons (Grp) (MkGrp r c) gs))))

(def-adts $ (Ins : ((Nat) n) ((List (Nat)) x) ((List (Grp)) gs) ((List (Grp)) hs) -> Type)
  enum
  (many InsHere : (erased (Nat) n) (erased (List (Nat)) x) (erased (List (Grp)) gs) (erased (Hd n x gs) h)
     -> (Ins n x gs (Cons (Grp) (MkGrp x (Succ (Zero))) gs)))
  (many InsEq : (erased (Nat) n) (erased (List (Nat)) x) (erased (Nat) c) (erased (List (Grp)) gs)
     -> (Ins n x (Cons (Grp) (MkGrp x c) gs) (Cons (Grp) (MkGrp x (Succ c)) gs)))
  (many InsSkip : (erased (Nat) n) (erased (List (Nat)) x r) (erased (Nat) c) (erased (List (Grp)) gs hs) (erased (RLt n x r) l)
     (erased (Ins n x gs hs) i) -> (Ins n x (Cons (Grp) (MkGrp r c) gs) (Cons (Grp) (MkGrp r c) hs))))

; Drop n r gs hs : hs is gs with one element of rank r removed and any elements of lower rank added.
(def-adts $ (Drop : ((Nat) n) ((List (Nat)) r) ((List (Grp)) gs) ((List (Grp)) hs) -> Type)
  enum
  (many DAbove : (erased (Nat) n) (erased (List (Nat)) r r2) (erased (Nat) c) (erased (List (Grp)) gs hs) (erased (RLt n r r2) l)
     (erased (Drop n r gs hs) d) -> (Drop n r (Cons (Grp) (MkGrp r2 c) gs) (Cons (Grp) (MkGrp r2 c) hs)))
  (many DHere : (erased (Nat) n) (erased (List (Nat)) r) (erased (Nat) c c2) (erased (List (Grp)) gs hs) (erased (Lt c2 c) l)
     (erased (Hd n r hs) h) -> (Drop n r (Cons (Grp) (MkGrp r c) gs) (Cons (Grp) (MkGrp r c2) hs)))
  (many DGone : (erased (Nat) n) (erased (List (Nat)) r) (erased (Nat) c) (erased (List (Grp)) gs hs) (erased (Lt (Zero) c) pos)
     (erased (Hd n r hs) h) -> (Drop n r (Cons (Grp) (MkGrp r c) gs) hs)))

(def-fns _ $ (many ins : (erased (Nat) n) (many (List (Nat)) x) (erased (Length (Nat) x n) lx) (subterm many (List (Grp)) gs)
    (erased (Desc n gs) d) -> (many (List (Grp)) hs) (erased (Ins n x gs hs) i))
  (let-match many gs (Cons _ g gs1) ((Nil _) (values (Cons (Grp) (MkGrp x (Succ (Zero))) gs) (InsHere n x gs (HdNil n x)))))
  (let-match many g (MkGrp r c))
  (let-match erased d (DcCons _ _ _ _ lr _ _ d1))
  (let-match many (rank-cmp n x r lx lr) (RCLt _ _ _ p l)
    ((RCGt _ _ _ p l) (values (Cons (Grp) (MkGrp x (Succ (Zero))) gs) (InsHere n x gs (HdCons n x r c gs1 (MkRLt n p r x l)))))
    ((RCEq _ _) (values (Cons (Grp) (MkGrp x (Succ c)) gs1) (InsEq n x c gs1))))
  (let ((many hs1) (erased i1)) (notail $ ins n x lx gs1 d1))
  (values (Cons (Grp) g hs1) (InsSkip n x r c gs1 hs1 (MkRLt n p x r l) i1)))

(def-fns _ $ (erased ins-hd : (erased (Nat) n) (erased (List (Nat)) x r) (erased (List (Grp)) gs hs) (subterm erased (Ins n x gs hs) i)
    (erased (Hd n r gs) h) (erased (RLt n x r) l) -> (erased (Hd n r hs) h2))
  (let-match erased i (InsSkip _ _ r2 c gs1 hs1 _ _)
    ((InsHere _ _ _ _) (HdCons n r x (Succ (Zero)) gs l))
    ((InsEq _ _ c _) (HdCons n r x (Succ c) _ l)))
  (let-match erased h (HdCons _ _ _ _ _ l2))
  (HdCons n r r2 c hs1 l2))

(def-fns _ $ (erased ins-desc : (erased (Nat) n) (erased (List (Nat)) x) (erased (List (Grp)) gs hs) (subterm erased (Ins n x gs hs) i)
    (erased (Length (Nat) x n) lx) (erased (Desc n gs) d) -> (erased (Desc n hs) d2))
  (match erased i _
    ((InsHere _ _ _ h) (DcCons n x (Succ (Zero)) gs lx (LtZ (Zero)) h d))
    ((InsEq _ _ c gs1)
      (let-match erased d (DcCons _ _ _ _ lr _ h d1))
      (DcCons n x (Succ c) gs1 lr (LtZ c) h d1))
    ((InsSkip _ _ r c gs1 hs1 l i1)
      (let-match erased d (DcCons _ _ _ _ lr pos h d1))
      (DcCons n r c hs1 lr pos (ins-hd n x r gs1 hs1 i1 h l) (ins-desc n x gs1 hs1 i1 lx d1)))))

(def-fns _ $ (erased ins-drop : (erased (Nat) n) (erased (List (Nat)) rd x) (erased (List (Grp)) a a2 b b2)
    (subterm erased (Drop n rd a a2) d) (erased (Ins n x a b) i1) (erased (Ins n x a2 b2) i2) -> (erased (Drop n rd b b2) e))
  (match erased d _
    ((DAbove _ _ r2 c gs hs l d1)
      (match erased i1 _
        ((InsHere _ _ _ h)
          (let-match erased h (HdCons _ _ _ _ _ lx))
          (let-match erased i2 (InsHere _ _ _ _)
            (absurd (InsEq _ _ _ _) (rlt-irrefl n x lx))
            (absurd (InsSkip _ _ _ _ _ _ l2 _) (rlt-asym n x r2 l2 lx)))
          (DAbove n rd x (Succ (Zero)) a a2 (rlt-trans n rd r2 x l lx) d))
        ((InsEq _ _ _ _)
          (let-match erased i2 (InsEq _ _ _ _)
            (absurd (InsHere _ _ _ h) (let-match erased h (HdCons _ _ _ _ _ l2)) (rlt-irrefl n x l2))
            (absurd (InsSkip _ _ _ _ _ _ l2 _) (rlt-irrefl n x l2)))
          (DAbove n rd r2 (Succ c) gs hs l d1))
        ((InsSkip _ _ _ _ _ gs2 lx j1)
          (let-match erased i2 (InsSkip _ _ _ _ _ hs2 _ j2)
            (absurd (InsHere _ _ _ h) (let-match erased h (HdCons _ _ _ _ _ l2)) (rlt-asym n x r2 lx l2))
            (absurd (InsEq _ _ _ _) (rlt-irrefl n x lx)))
          (DAbove n rd r2 c gs2 hs2 l (ins-drop n rd x gs hs gs2 hs2 d1 j1 j2)))))
    ((DHere _ _ c c2 gs hs lt h)
      (match erased i1 _
        ((InsHere _ _ _ hx)
          (let-match erased hx (HdCons _ _ _ _ _ lx))
          (let-match erased i2 (InsHere _ _ _ _)
            (absurd (InsEq _ _ _ _) (rlt-irrefl n x lx))
            (absurd (InsSkip _ _ _ _ _ _ l2 _) (rlt-asym n x rd l2 lx)))
          (DAbove n rd x (Succ (Zero)) a a2 lx d))
        ((InsEq _ _ _ _)
          (let-match erased i2 (InsEq _ _ _ _)
            (absurd (InsHere _ _ _ hx) (let-match erased hx (HdCons _ _ _ _ _ l2)) (rlt-irrefl n x l2))
            (absurd (InsSkip _ _ _ _ _ _ l2 _) (rlt-irrefl n x l2)))
          (DHere n rd (Succ c) (Succ c2) gs hs (LtS c2 c lt) h))
        ((InsSkip _ _ _ _ _ gs2 lx j1)
          (let-match erased i2 (InsSkip _ _ _ _ _ hs2 _ j2)
            (absurd (InsHere _ _ _ hx) (let-match erased hx (HdCons _ _ _ _ _ l2)) (rlt-asym n x rd lx l2))
            (absurd (InsEq _ _ _ _) (rlt-irrefl n x lx)))
          (DHere n rd c c2 gs2 hs2 lt (ins-hd n x rd hs hs2 j2 h lx)))))
    ((DGone _ _ c gs hs pos h)
      (match erased i1 _
        ((InsHere _ _ _ hx)
          (let-match erased hx (HdCons _ _ _ _ _ lx))
          (let-match erased i2 (InsHere _ _ _ _)
            (absurd (InsEq _ _ _ _) (let-match erased h (HdCons _ _ _ _ _ l2)) (rlt-asym n x rd l2 lx))
            (absurd (InsSkip _ _ r3 _ _ _ l2 _)
              (let-match erased h (HdCons _ _ _ _ _ l3))
              (rlt-asym n x rd (rlt-trans n x r3 rd l2 l3) lx)))
          (DAbove n rd x (Succ (Zero)) a hs lx d))
        ((InsEq _ _ _ _)
          (let-match erased i2 (InsHere _ _ _ _)
            (absurd (InsEq _ _ _ _) (let-match erased h (HdCons _ _ _ _ _ l2)) (rlt-irrefl n x l2))
            (absurd (InsSkip _ _ r3 _ _ _ l2 _) (let-match erased h (HdCons _ _ _ _ _ l3)) (rlt-asym n x r3 l2 l3)))
          (DHere n rd (Succ c) (Succ (Zero)) gs hs (LtS (Zero) c pos) h))
        ((InsSkip _ _ _ _ _ gs2 lx j1)
          (DGone n rd c gs2 b2 pos (ins-hd n x rd hs b2 i2 h lx)))))))

(def-fns _ $ (erased drop-compose : (erased (Nat) n) (erased (List (Nat)) rd rd2) (erased (List (Grp)) m m2 m3)
    (erased (Drop n rd m m2) d1) (subterm erased (Drop n rd2 m2 m3) d2) (erased (RLt n rd rd2) l) -> (erased (Drop n rd2 m m3) d))
  (match erased d2 _
    ((DAbove _ _ r2 c gs hs l2 d3)
      (let-match erased d1 (DAbove _ _ _ _ gs0 _ _ d4)
        (absurd (DHere _ _ _ _ _ _ _ _) (rlt-asym n rd rd2 l l2))
        (absurd (DGone _ _ _ _ _ _ h) (let-match erased h (HdCons _ _ _ _ _ l3)) (rlt-asym n rd r2 (rlt-trans n rd rd2 r2 l l2) l3)))
      (DAbove n rd2 r2 c gs0 hs l2 (drop-compose n rd rd2 gs0 gs hs d4 d3 l)))
    ((DHere _ _ c c2 gs hs lt h)
      (let-match erased d1 (DAbove _ _ _ _ gs0 _ _ _)
        (absurd (DHere _ _ _ _ _ _ _ _) (rlt-irrefl n rd l))
        (absurd (DGone _ _ _ _ _ _ h2) (let-match erased h2 (HdCons _ _ _ _ _ l3)) (rlt-asym n rd rd2 l l3)))
      (DHere n rd2 c c2 gs0 hs lt h))
    ((DGone _ _ c gs hs pos h)
      (let-match erased d1 (DAbove _ _ _ _ gs0 _ _ _)
        (absurd (DHere _ _ _ _ _ _ _ _) (rlt-irrefl n rd l))
        (absurd (DGone _ _ _ _ _ _ h2) (let-match erased h2 (HdCons _ _ _ _ _ l3)) (rlt-asym n rd rd2 l l3)))
      (DGone n rd2 c gs0 hs pos h))))

; m is t after q groups, each of rank above r.
(def-adts $ (Ctx : ((Nat) n) ((List (Nat)) r) ((Nat) q) ((List (Grp)) m) ((List (Grp)) t) -> Type)
  enum
  (many CtxHere : (erased (Nat) n) (erased (List (Nat)) r) (erased (List (Grp)) t) -> (Ctx n r (Zero) t t))
  (many CtxCons : (erased (Nat) n) (erased (List (Nat)) r r2) (erased (Nat) c q) (erased (List (Grp)) m t) (erased (RLt n r r2) l)
     (erased (Ctx n r q m t) x) -> (Ctx n r (Succ q) (Cons (Grp) (MkGrp r2 c) m) t)))

(def-adts $ (Skip : ((Nat) q) ((List (Grp)) m) ((List (Grp)) t) -> Type)
  enum
  (many SkZ : (erased (List (Grp)) m) -> (Skip (Zero) m m))
  (many SkS : (erased (Nat) q) (erased (Grp) g) (erased (List (Grp)) m t) (erased (Skip q m t) s) -> (Skip (Succ q) (Cons (Grp) g m) t)))

(def-fns _ $ (many skip : (subterm many (Nat) q) (many (List (Grp)) m) (erased (List (Nat)) r) (erased (Nat) n) (erased (List (Grp)) t)
    (erased (Ctx n r q m t) x) -> (many t is u))
  (let-match many q (Succ q1) ((Zero) (let-match erased x (CtxHere _ _ _)) m))
  (let-match erased x (CtxCons _ _ _ _ _ m1 _ _ x1))
  (let-match many m (Cons _ _ m2))
  (tail $ skip q1 m2 r n t x1))

(def-fns _ $ (erased ctx-weaken : (erased (Nat) n q) (erased (List (Nat)) r r2) (erased (List (Grp)) m t) (subterm erased (Ctx n r q m t) x)
    (erased (RLt n r2 r) l) -> (erased (Ctx n r2 q m t) y))
  (match erased x _
    ((CtxHere _ _ _) (CtxHere n r2 t))
    ((CtxCons _ _ r3 c q1 m1 _ l1 x1) (CtxCons n r2 r3 c q1 m1 t (rlt-trans n r2 r r3 l l1) (ctx-weaken n q1 r r2 m1 t x1 l)))))

(def-fns _ $ (erased ctx-next : (erased (Nat) n q) (erased (List (Nat)) r r2) (erased (Nat) c c2) (erased (List (Grp)) m t)
    (subterm erased (Ctx n r q m (Cons (Grp) (MkGrp r c) (Cons (Grp) (MkGrp r2 c2) t))) x) (erased (RLt n r2 r) l)
    -> (erased (Ctx n r2 (Succ q) m (Cons (Grp) (MkGrp r2 c2) t)) y))
  (match erased x _
    ((CtxHere _ _ _)
      (CtxCons n r2 r c (Zero) (Cons (Grp) (MkGrp r2 c2) t) _ l (CtxHere n r2 (Cons (Grp) (MkGrp r2 c2) t))))
    ((CtxCons _ _ r3 c3 q1 m1 _ l1 x1)
      (CtxCons n r2 r3 c3 (Succ q1) m1 _ (rlt-trans n r2 r r3 l l1) (ctx-next n q1 r r2 c c2 m1 t x1 l)))))

(def-fns _ $ (erased ctx-desc : (erased (Nat) n q) (erased (List (Nat)) r) (erased (List (Grp)) m t) (subterm erased (Ctx n r q m t) x)
    (erased (Desc n m) d) -> (erased (Desc n t) e))
  (let-match erased x (CtxCons _ _ _ _ q1 m1 _ _ x1) ((CtxHere _ _ _) d))
  (let-match erased d (DcCons _ _ _ _ _ _ _ d1))
  (ctx-desc n q1 r m1 t x1 d1))

(def-fns _ $ (erased absurd drop-hd : (erased (Nat) n) (erased (List (Nat)) rd) (erased (List (Grp)) t t2)
    (erased (Drop n rd t t2) d) (erased (Hd n rd t) h) -> (erased (False) f))
  (let-match erased h (HdCons _ _ r2 _ _ l) (absurd (HdNil _ _) (match erased d _)))
  (match erased d _
    (absurd (DAbove _ _ _ _ _ _ l2 _) (rlt-asym n rd r2 l2 l))
    (absurd (DHere _ _ _ _ _ _ _ _) (rlt-irrefl n rd l))
    (absurd (DGone _ _ _ _ _ _ _) (rlt-irrefl n rd l))))

(def-adts $ (Split3 : ((Nat) n) ((List (Nat)) r rd) ((Nat) q c) ((List (Grp)) m2) -> Type)
  enum
  (many SpAbove : (erased (Nat) n) (erased (List (Nat)) r rd) (erased (Nat) q c) (erased (List (Grp)) m2) (erased (RLt n r rd) l)
     -> (Split3 n r rd q c m2))
  (many SpHere : (erased (Nat) n) (erased (List (Nat)) r) (erased (Nat) q c c2) (erased (List (Grp)) m2 t2) (erased (Lt c2 c) l)
     (erased (Ctx n r q m2 (Cons (Grp) (MkGrp r c2) t2)) x) -> (Split3 n r r q c m2))
  (many SpGone : (erased (Nat) n) (erased (List (Nat)) r) (erased (Nat) q c) (erased (List (Grp)) m2 t2)
     (erased (Ctx n r q m2 t2) x) (erased (Hd n r t2) h) -> (Split3 n r r q c m2)))

(def-fns _ $ (erased drop-split : (erased (Nat) n q c) (erased (List (Nat)) r rd) (erased (List (Grp)) m t m2)
    (subterm erased (Ctx n r q m (Cons (Grp) (MkGrp r c) t)) x) (erased (Drop n rd m m2) d) (erased (Hd n rd t) h)
    -> (erased (Split3 n r rd q c m2) s))
  (match erased x _
    ((CtxHere _ _ _)
      (match erased d _
        (absurd (DAbove _ _ _ _ _ _ _ d1) (drop-hd n rd t _ d1 h))
        ((DHere _ _ _ c2 _ hs lt _) (SpHere n r q c c2 m2 hs lt (CtxHere n r (Cons (Grp) (MkGrp r c2) hs))))
        ((DGone _ _ _ _ hs _ h2) (SpGone n r q c m2 m2 (CtxHere n r m2) h2))))
    ((CtxCons _ _ r2 c3 q1 m1 _ l x1)
      (let-match erased d (DAbove _ _ _ _ _ m21 _ d1)
        ((DHere _ _ _ _ _ _ _ _) (SpAbove n r rd q c m2 l))
        ((DGone _ _ _ _ _ _ _) (SpAbove n r rd q c m2 l)))
      (match erased (drop-split n q1 c r rd m1 t m21 x1 d1 h) _
        ((SpAbove _ _ _ _ _ _ l2) (SpAbove n r rd q c m2 l2))
        ((SpHere _ _ _ _ c2 _ t2 lt x2)
          (SpHere n r q c c2 m2 t2 lt (CtxCons n r r2 c3 q1 m21 (Cons (Grp) (MkGrp r c2) t2) l x2)))
        ((SpGone _ _ _ _ _ t2 x2 h2) (SpGone n r q c m2 t2 (CtxCons n r r2 c3 q1 m21 t2 l x2) h2))))))

(def-adts $ (ShapeR : ((Nat) n) ((List (Nat)) r) ((Nat) c) ((List (Grp)) t) -> Type)
  enum
  (many ShHere : (erased (Nat) n) (erased (List (Nat)) r) (erased (Nat) c c2) (erased (List (Grp)) t2) (erased (Lt c2 c) l)
     -> (ShapeR n r c (Cons (Grp) (MkGrp r c2) t2)))
  (many ShGone : (erased (Nat) n) (erased (List (Nat)) r) (erased (Nat) c) (erased (List (Grp)) t) (erased (Hd n r t) h)
     -> (ShapeR n r c t)))

(def-fns _ $ (erased split-eq : (erased (Nat) n q c) (erased (List (Nat)) r) (erased (List (Grp)) m2) (erased (Split3 n r r q c m2) s)
    -> (erased (List (Grp)) t2) (erased (Ctx n r q m2 t2) x) (erased (ShapeR n r c t2) sh))
  (match erased s _
    (absurd (SpAbove _ _ _ _ _ _ l) (rlt-irrefl n r l))
    ((SpHere _ _ _ _ c2 _ t2 lt x) (values (Cons (Grp) (MkGrp r c2) t2) x (ShHere n r c c2 t2 lt)))
    ((SpGone _ _ _ _ _ t2 x h) (values t2 x (ShGone n r c t2 h)))))

(def-fns _ $ (erased drop-ctx-above : (erased (Nat) n q) (erased (List (Nat)) r rd) (erased (List (Grp)) m2 m3 t2)
    (subterm erased (Ctx n r q m2 t2) x) (erased (Drop n rd m2 m3) d) (erased (Hd n rd t2) h) -> (erased (RLt n r rd) l))
  (match erased x _
    ((CtxHere _ _ _) (match erased (drop-hd n rd t2 m3 d h) _))
    ((CtxCons _ _ r2 _ q1 m1 _ l1 x1)
      (match erased d _
        ((DAbove _ _ _ _ _ m31 _ d1) (drop-ctx-above n q1 r rd m1 m31 t2 x1 d1 h))
        ((DHere _ _ _ _ _ _ _ _) l1)
        ((DGone _ _ _ _ _ _ _) l1)))))

(def-fns _ $ (erased drop-length : (erased (Nat) n) (erased (List (Nat)) rd) (erased (List (Grp)) m m2) (subterm erased (Drop n rd m m2) d)
    (erased (Desc n m) e) -> (erased (Length (Nat) rd n) l))
  (let-match erased e (DcCons _ _ _ _ ln _ _ e1) (absurd (DcNil _) (match erased d _)))
  (match erased d _
    ((DAbove _ _ _ _ gs _ _ d1) (drop-length n rd gs _ d1 e1))
    ((DHere _ _ _ _ _ _ _ _) ln)
    ((DGone _ _ _ _ _ _ _) ln)))

(def-fns _ $ (erased absurd drop-top : (erased (Nat) n) (erased (List (Nat)) r rd) (erased (Nat) c) (erased (List (Grp)) t m2)
    (erased (Drop n rd (Cons (Grp) (MkGrp r c) t) m2) d) (erased (RLt n r rd) l) -> (erased (False) f))
  (match erased d _
    (absurd (DAbove _ _ _ _ _ _ l2 _) (rlt-asym n rd r l2 l))
    (absurd (DHere _ _ _ _ _ _ _ _) (rlt-irrefl n rd l))
    (absurd (DGone _ _ _ _ _ _ _) (rlt-irrefl n rd l))))

; S : the state type, indexed by the multiset measure m; R : the result type; n : the length of a rank.
(def-adts $ (DStep : ((TyCtor ((List (Grp)) m) -> Type) S) (Type R) ((Nat) n) ((List (Grp)) m) -> Type)
  enum
  (many DSDone : (erased (TyCtor ((List (Grp)) m) -> Type) S) (erased Type R) (erased (Nat) n) (erased (List (Grp)) m)
     (many R x) -> (DStep S R n m))
  (many DSNext : (erased (TyCtor ((List (Grp)) m) -> Type) S) (erased Type R) (erased (Nat) n) (erased (List (Grp)) m)
     (many (List (Grp)) m2) (many (S m2) s) (many (List (Nat)) rd) (erased (Drop n rd m m2) d) (erased (Desc n m2) e)
     -> (DStep S R n m)))

; r : the rank of the frame's group; an exit lowered a group of a rank rd above it.
(def-adts $ (DOut : ((TyCtor ((List (Grp)) m) -> Type) S) (Type R) ((Nat) n) ((List (Nat)) r) ((List (Grp)) m) -> Type)
  enum
  (many DODone : (erased (TyCtor ((List (Grp)) m) -> Type) S) (erased Type R) (erased (Nat) n) (erased (List (Nat)) r)
     (erased (List (Grp)) m) (many R x) -> (DOut S R n r m))
  (many DOExit : (erased (TyCtor ((List (Grp)) m) -> Type) S) (erased Type R) (erased (Nat) n) (erased (List (Nat)) r)
     (erased (List (Grp)) m) (many (List (Grp)) m2) (many (S m2) s) (many (List (Nat)) rd) (erased (RLt n r rd) l)
     (erased (Drop n rd m m2) d) (erased (Desc n m2) e) -> (DOut S R n r m)))

; t : the groups after the frame's own; an exit lowered a group of a rank rd above all of t.
(def-adts $ (DIn : ((TyCtor ((List (Grp)) m) -> Type) S) (Type R) ((Nat) n) ((List (Grp)) t) ((List (Grp)) m) -> Type)
  enum
  (many DIDone : (erased (TyCtor ((List (Grp)) m) -> Type) S) (erased Type R) (erased (Nat) n) (erased (List (Grp)) t)
     (erased (List (Grp)) m) (many R x) -> (DIn S R n t m))
  (many DIExit : (erased (TyCtor ((List (Grp)) m) -> Type) S) (erased Type R) (erased (Nat) n) (erased (List (Grp)) t)
     (erased (List (Grp)) m) (many (List (Grp)) m2) (many (S m2) s) (many (List (Nat)) rd) (erased (Hd n rd t) h)
     (erased (Drop n rd m m2) d) (erased (Desc n m2) e) -> (DIn S R n t m)))
