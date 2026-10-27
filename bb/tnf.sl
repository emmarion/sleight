
(def-adts
  ((PLookR : ((List (PT)) p) ((Nat) q) ((Bool) b) -> Type)
    enum
    (many PLOk : (erased (List (PT)) p) (erased (Nat) q) (erased (Bool) b) (many (PT) x) (erased (PLook p q b x) pl) -> (PLookR p q b))
    (many PLNo : (erased (List (PT)) p) (erased (Nat) q) (erased (Bool) b) -> (PLookR p q b))))

(def-fns _ $ (many plook : (subterm many (List (PT)) p) (many (Nat) q) (many (Bool) b) -> (many (PLookR p q b) r))
  (let-match many p (Cons _ x0 p1) ((Nil _) (PLNo p q b)))
  (let-match many p1 (Cons _ x1 rest) ((Nil _) (PLNo p q b)))
  (match many q _
    ((Zero) (match many b _ ((BFalse) (PLOk p q b x0 (PL0 x0 x1 rest))) ((BTrue) (PLOk p q b x1 (PL1 x0 x1 rest)))))
    ((Succ q1)
      (let-match many (notail $ plook rest q1 b) (PLOk _ _ _ x pl) ((PLNo _ _ _) (PLNo p q b)))
      (PLOk p q b x (PLS x0 x1 rest q1 b x pl)))))

(def-adts
  ((PSetR : ((List (PT)) p) ((Nat) q) ((Bool) b) ((PT) y) -> Type)
    enum
    (many PSOk : (erased (List (PT)) p) (erased (Nat) q) (erased (Bool) b) (erased (PT) y) (many (List (PT)) p2) (erased (PSet p q b y p2) ps) -> (PSetR p q b y))
    (many PSNo : (erased (List (PT)) p) (erased (Nat) q) (erased (Bool) b) (erased (PT) y) -> (PSetR p q b y))))

(def-fns _ $ (many pset : (subterm many (List (PT)) p) (many (Nat) q) (many (Bool) b) (many (PT) y) -> (many (PSetR p q b y) r))
  (let-match many p (Cons _ x0 p1) ((Nil _) (PSNo p q b y)))
  (let-match many p1 (Cons _ x1 rest) ((Nil _) (PSNo p q b y)))
  (match many q _
    ((Zero)
      (match many b _
        ((BFalse) (PSOk p q b y (Cons (PT) y (Cons (PT) x1 rest)) (PS0 x0 x1 y rest)))
        ((BTrue) (PSOk p q b y (Cons (PT) x0 (Cons (PT) y rest)) (PS1 x0 x1 y rest)))))
    ((Succ q1)
      (let-match many (notail $ pset rest q1 b y) (PSOk _ _ _ _ rest2 ps) ((PSNo _ _ _ _) (PSNo p q b y)))
      (PSOk p q b y (Cons (PT) x0 (Cons (PT) x1 rest2)) (PSS x0 x1 y rest rest2 q1 b ps)))))

(def-adts
  ((PSimR : ((List (PT)) p) -> Type)
    enum
    (many PSHalt : (erased (List (PT)) p) (many (Nat) t) (erased (Nat) q) (erased (List (Bool)) l r) (erased (Bool) h)
       (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t (MkCfg q l h r)) pr) (erased (PLook p q h (Def (Halt))) pl) -> (PSimR p))
    (many PSUndef : (erased (List (PT)) p) (erased (Nat) t) (many (Nat) q) (erased (List (Bool)) l r) (many (Bool) h)
       (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t (MkCfg q l h r)) pr) (erased (PLook p q h (Undef)) pl) -> (PSimR p))
    (many PSOut : (erased (List (PT)) p) (many (Nat) t q) (many (List (Bool)) l r) (many (Bool) h)
       (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t (MkCfg q l h r)) pr) -> (PSimR p))))

(def-fns _ $ (many psim : (many (List (PT)) p) (subterm many (Nat) fuel) (many (Nat) t q) (many (List (Bool)) l) (many (Bool) h) (many (List (Bool)) r)
    (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t (MkCfg q l h r)) pr) -> (many (PSimR p) res))
  (let-match many fuel (Succ f) ((Zero) (PSOut p t q l r h pr)))
  (let-match many (plook p q h) (PLOk _ _ _ x pl) ((PLNo _ _ _) (PSOut p t q l r h pr)))
  (let-match many x (Def tr) ((Undef) (PSUndef p t q l r h pr pl)))
  (let-match many tr (Go w d q2) ((Halt) (PSHalt p t q l r h pr pl)))
  (match many d _
    ((DL)
      (match many l _
        ((Nil _) (tail $ psim p f (Succ t) q2 l (BFalse) (Cons (Bool) w r)
          (PRSnoc p _ _ _ t pr (PStepL p q q2 l r l h w (BFalse) pl (PopNil)))))
        ((Cons _ h2 l2) (tail $ psim p f (Succ t) q2 l2 h2 (Cons (Bool) w r)
          (PRSnoc p _ _ _ t pr (PStepL p q q2 l r l2 h w h2 pl (PopCons h2 l2)))))))
    ((DR)
      (match many r _
        ((Nil _) (tail $ psim p f (Succ t) q2 (Cons (Bool) w l) (BFalse) r
          (PRSnoc p _ _ _ t pr (PStepR p q q2 l r r h w (BFalse) pl (PopNil)))))
        ((Cons _ h2 r2) (tail $ psim p f (Succ t) q2 (Cons (Bool) w l) h2 r2
          (PRSnoc p _ _ _ t pr (PStepR p q q2 l r r2 h w h2 pl (PopCons h2 r2)))))))))

(def-adts $ (Choice : -> Type)
  enum
  (many MkCh : (many (Nat) cn o2) (many (List (Nat)) tg) -> (Choice)))

(def-adts $ (Cert : -> Type)
  enum
  (many MkCert : (many (List (Bool)) sy) (many (List (List (Pair (Nat) (Nat)))) adj) (many (List (Nat)) acc) (many (List (ACN)) S)
     (many (List (Choice)) ch) (many (ACN) a0) -> (Cert)))

(def-adts
  ((NthR : (Type A) ((List A) xs) ((Nat) i) -> Type)
    enum
    (many NOk : (erased Type A) (erased (List A) xs) (erased (Nat) i) (many A x) (erased (Nth A xs i x) p) -> (NthR A xs i))
    (many NNo : (erased Type A) (erased (List A) xs) (erased (Nat) i) -> (NthR A xs i))))

(def-adts
  ((CopyL : (Type A) ((List A) xs) ((List (Copy A)) ys) -> Type)
    enum
    (many CLNil : (erased Type A) -> (CopyL A (Nil A) (Nil (Copy A))))
    (many CLCons : (erased Type A) (erased A x) (erased (List A) xs) (erased (List (Copy A)) ys) (erased (CopyL A xs ys) r)
       -> (CopyL A (Cons A x xs) (Cons (Copy A) (MkCopy A x) ys)))))

(def-fns _ $ (many copies : (erased Type A) (subterm many (List A) xs) -> (many (List (Copy A)) ys) (erased (CopyL A xs ys) c))
  (let-match many xs (Cons _ x rest) ((Nil _) (values (Nil (Copy A)) (CLNil A))))
  (let ((many ys) (erased c)) (notail $ copies A rest))
  (values (Cons (Copy A) (MkCopy A x) ys) (CLCons A x rest ys c)))

(def-fns _ $ (erased copy-nth : (erased Type A) (erased (List A) xs) (erased (List (Copy A)) ys) (erased (Nat) i) (erased A x)
    (erased (CopyL A xs ys) c) (subterm erased (Nth (Copy A) ys i (MkCopy A x)) p) -> (erased (Nth A xs i x) q))
  (match erased p _
    ((NthHere _ _ rest) (let-match erased c (CLCons _ _ xs1 _ _)) (NthHere A x xs1))
    ((NthThere _ _ rest i1 _ p1)
      (let-match erased c (CLCons _ x0 xs1 _ c1))
      (NthThere A x0 xs1 i1 x (copy-nth A xs1 rest i1 x c1 p1)))))

(def-adts
  ((AV : (Type A) ((List A) xs) -> Type)
    enum
    (many MkAV : (erased Type A) (erased (List A) xs) (erased (List (Copy A)) ys) (many (Array (Copy A) ys) ar) (many (Nat) n)
       (erased (Length (Copy A) ys n) ln) (erased (CopyL A xs ys) cl) -> (AV A xs))))

(def-fns _ $ (many mk-av : (erased Type A) (many (List A) xs) -> (many (AV A xs) v))
  (let ((many ys) (erased cl)) (copies A xs))
  (let ((unique au)) (list-to-array A ys))
  (let ((many ar)) (share au))
  (let ((many n) (erased ln)) (array-length-many _ _ ar))
  (MkAV A xs ys ar n ln cl))

(def-fns _ $ (many aget : (erased Type A) (erased (List A) xs) (many (AV A xs) v) (many (Nat) i) -> (many (NthR A xs i) r))
  (let-match many v (MkAV _ _ ys ar n ln cl))
  (let-match many (lt-dec i n) (Yes _ _ _ _ lt) ((No _ _ _ _ _) (NNo A xs i)))
  (let ((erased y) (erased ny)) (lt-nth (Copy A) ys n i ln lt))
  (let ((many cell)) (array-get-many _ _ ar i y ny))
  (let-match many cell (MkCopy _ x))
  (NOk A xs i x (copy-nth A xs ys i x cl ny)))

(def-fns _ $ (erased nth-mem : (erased Type A) (erased (List A) xs) (erased (Nat) i) (erased A x) (subterm erased (Nth A xs i x) p) ->
    (erased (Mem A x xs) m))
  (match erased p _
    ((NthHere _ _ rest) (MemHere A x rest))
    ((NthThere _ y rest i1 _ p1) (MemThere A x y rest (nth-mem A rest i1 x p1)))))

(def-adts
  ((All : (Type A) ((TyCtor (A x) -> Type) P) ((List A) xs) -> Type)
    enum
    (many AllNil : (erased Type A) (erased (TyCtor (A x) -> Type) P) -> (All A P (Nil A)))
    (many AllCons : (erased Type A) (erased (TyCtor (A x) -> Type) P) (erased A x) (erased (List A) xs) (erased (P x) px) (erased (All A P xs) r)
       -> (All A P (Cons A x xs)))))

(def-adts
  ((BdN : ((Nat) x) -> Type)
    enum
    (many MkBdN : (erased (Nat) x) (erased (Lt x B40) p) -> (BdN x))))

(def-adts
  ((BdA : ((ACN) a) -> Type)
    enum
    (many MkBdA : (erased (Nat) q sl sh sr) (erased (Lt q B40) a) (erased (Lt sl B40) b) (erased (Lt sh B40) c) (erased (Lt sr B40) d)
       -> (BdA (MkACN q sl sh sr)))))

(def-adts
  ((BdP : ((Pair (Nat) (Nat)) c) -> Type)
    enum
    (many MkBdP : (erased (Nat) a b) (erased (Lt a B40) pa) (erased (Lt b B40) pb) -> (BdP (MkPair (Nat) (Nat) a b)))))

(def-adts
  ((BdRow : ((List (Pair (Nat) (Nat))) row) -> Type)
    enum
    (many MkBdRow : (erased (List (Pair (Nat) (Nat))) row) (erased (All (Pair (Nat) (Nat)) BdP row) b) -> (BdRow row))))

(def-adts
  ((BdC : ((Choice) c) -> Type)
    enum
    (many MkBdC : (erased (Nat) cn o2) (erased (List (Nat)) tg) (erased (Lt cn B40) pc) (erased (Lt o2 B40) po) -> (BdC (MkCh cn o2 tg)))))

(def-fns _ $ (erased all-nth : (erased Type A) (erased (TyCtor (A x) -> Type) P) (erased (List A) xs) (erased (Nat) i) (erased A x)
    (subterm erased (All A P xs) al) (erased (Nth A xs i x) n) -> (erased (P x) px))
  (match erased n _
    ((NthHere _ _ _) (let-match erased al (AllCons _ _ _ _ px _)) px)
    ((NthThere _ _ rest i1 _ n1) (let-match erased al (AllCons _ _ _ _ _ al1)) (all-nth A P rest i1 x al1 n1))))

(def-fns _ $ (many beq : (many (Nat) x y) (erased (Lt x B40) px) (erased (Lt y B40) py) -> (many (EqDec (Nat) Lt x y) e))
  (tail $ u62-eq x y (lt-trans x B40 u62-modulus px NM40) (lt-trans y B40 u62-modulus py NM40)))

(def-fns _ $ (many bd : (many (Nat) x) -> (many (Res (Lt x B40)) r))
  (match many (lt-dec x B40) _ ((Yes _ _ _ _ p) (ROk _ p)) ((No _ _ _ _ _) (RFail _))))

(def-fns _ $ (many bd-acns : (subterm many (List (ACN)) xs) -> (many (Res (All (ACN) BdA xs)) r))
  (let-match many xs (Cons _ a rest) ((Nil _) (ROk _ (AllNil (ACN) BdA))))
  (let-match many a (MkACN q sl sh sr))
  (let-match many (bd q) (ROk _ pq) ((RFail _) (RFail _)))
  (let-match many (bd sl) (ROk _ pl) ((RFail _) (RFail _)))
  (let-match many (bd sh) (ROk _ ph) ((RFail _) (RFail _)))
  (let-match many (bd sr) (ROk _ pr) ((RFail _) (RFail _)))
  (let-match many (notail $ bd-acns rest) (ROk _ r) ((RFail _) (RFail _)))
  (ROk _ (AllCons (ACN) BdA a rest (MkBdA q sl sh sr pq pl ph pr) r)))

(def-fns _ $ (many bd-nats : (subterm many (List (Nat)) xs) -> (many (Res (All (Nat) BdN xs)) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (ROk _ (AllNil (Nat) BdN))))
  (let-match many (bd x) (ROk _ px) ((RFail _) (RFail _)))
  (let-match many (notail $ bd-nats rest) (ROk _ r) ((RFail _) (RFail _)))
  (ROk _ (AllCons (Nat) BdN x rest (MkBdN x px) r)))

(def-fns _ $ (many bd-pairs : (subterm many (List (Pair (Nat) (Nat))) xs) -> (many (Res (All (Pair (Nat) (Nat)) BdP xs)) r))
  (let-match many xs (Cons _ c rest) ((Nil _) (ROk _ (AllNil (Pair (Nat) (Nat)) BdP))))
  (let-match many c (MkPair _ _ a b))
  (let-match many (bd a) (ROk _ pa) ((RFail _) (RFail _)))
  (let-match many (bd b) (ROk _ pb) ((RFail _) (RFail _)))
  (let-match many (notail $ bd-pairs rest) (ROk _ r) ((RFail _) (RFail _)))
  (ROk _ (AllCons (Pair (Nat) (Nat)) BdP c rest (MkBdP a b pa pb) r)))

(def-fns _ $ (many bd-rows : (subterm many (List (List (Pair (Nat) (Nat)))) xs) -> (many (Res (All (List (Pair (Nat) (Nat))) BdRow xs)) r))
  (let-match many xs (Cons _ row rest) ((Nil _) (ROk _ (AllNil (List (Pair (Nat) (Nat))) BdRow))))
  (let-match many (bd-pairs row) (ROk _ b) ((RFail _) (RFail _)))
  (let-match many (notail $ bd-rows rest) (ROk _ r) ((RFail _) (RFail _)))
  (ROk _ (AllCons (List (Pair (Nat) (Nat))) BdRow row rest (MkBdRow row b) r)))

(def-fns _ $ (many bd-chs : (subterm many (List (Choice)) xs) -> (many (Res (All (Choice) BdC xs)) r))
  (let-match many xs (Cons _ c rest) ((Nil _) (ROk _ (AllNil (Choice) BdC))))
  (let-match many c (MkCh cn o2 tg))
  (let-match many (bd cn) (ROk _ pc) ((RFail _) (RFail _)))
  (let-match many (bd o2) (ROk _ po) ((RFail _) (RFail _)))
  (let-match many (notail $ bd-chs rest) (ROk _ r) ((RFail _) (RFail _)))
  (ROk _ (AllCons (Choice) BdC c rest (MkBdC cn o2 tg pc po) r)))

(def-fns _ $ (many eq-acn : (many (ACN) x) (many (ACN) y) (erased (BdA x) bx) (erased (BdA y) by) -> (many (Maybe (Eq (ACN) x y)) r))
  (let-match many x (MkACN a1 b1 c1 d1))
  (let-match many y (MkACN a2 b2 c2 d2))
  (let-match erased bx (MkBdA _ _ _ _ pa1 pb1 pc1 pd1))
  (let-match erased by (MkBdA _ _ _ _ pa2 pb2 pc2 pd2))
  (let-match many (beq a1 a2 pa1 pa2) (Equal _ _ _) (else (None _)))
  (let-match many (beq b1 b2 pb1 pb2) (Equal _ _ _) (else (None _)))
  (let-match many (beq c1 c2 pc1 pc2) (Equal _ _ _) (else (None _)))
  (let-match many (beq d1 d2 pd1 pd2) (Equal _ _ _) (else (None _)))
  (Some _ (Refl (ACN) x)))

(def-fns _ $ (many find-acn : (many (ACN) a) (subterm many (List (ACN)) xs) (erased (BdA a) ba) (erased (All (ACN) BdA xs) bs) ->
    (many (Res (Mem (ACN) a xs)) r))
  (let-match many xs (Cons _ b rest) ((Nil _) (RFail _)))
  (let-match erased bs (AllCons _ _ _ _ bb bs1))
  (match many (eq-acn a b ba bb) _
    ((Some _ e) (let-match many e (Refl _ _)) (ROk _ (MemHere (ACN) a rest)))
    ((None _)
      (let-match many (notail $ find-acn a rest ba bs1) (ROk _ mm) ((RFail _) (RFail _)))
      (ROk _ (MemThere (ACN) a b rest mm)))))

(def-fns _ $ (many find-pair : (many (Nat) c s2) (subterm many (List (Pair (Nat) (Nat))) row) (erased (Lt c B40) pc) (erased (Lt s2 B40) p2)
    (erased (All (Pair (Nat) (Nat)) BdP row) br) -> (many (Res (Mem (Pair (Nat) (Nat)) (MkPair (Nat) (Nat) c s2) row)) r))
  (let-match many row (Cons _ e rest) ((Nil _) (RFail _)))
  (let-match erased br (AllCons _ _ _ _ be br1))
  (let-match many e (MkPair _ _ c1 s3))
  (let-match erased be (MkBdP _ _ pc1 p3))
  (let ((many next))
    (match many (notail $ find-pair c s2 rest pc p2 br1) (((Res (Mem (Pair (Nat) (Nat)) (MkPair (Nat) (Nat) c s2) row)) x))
      ((ROk _ mm) (ROk _ (MemThere _ _ e rest mm)))
      ((RFail _) (RFail _))))
  (let-match many (beq c c1 pc pc1) (Equal _ _ _) (else next))
  (let-match many (beq s2 s3 p2 p3) (Equal _ _ _) (else next))
  (ROk _ (MemHere _ _ rest)))

(def-fns _ $ (many find-nat : (many (Nat) a) (subterm many (List (Nat)) xs) (erased (Lt a B40) ba) (erased (All (Nat) BdN xs) bs) ->
    (many (Res (Mem (Nat) a xs)) r))
  (let-match many xs (Cons _ b rest) ((Nil _) (RFail _)))
  (let-match erased bs (AllCons _ _ _ _ bb bs1))
  (let-match erased bb (MkBdN _ pb))
  (let-match many (beq a b ba pb) (Unequal _ _ _ _ _) ((Equal _ _ _) (ROk _ (MemHere (Nat) a rest))))
  (let-match many (notail $ find-nat a rest ba bs1) (ROk _ mm) ((RFail _) (RFail _)))
  (ROk _ (MemThere (Nat) a b rest mm)))

(def-fns _ $ (many place-n : (many (Dir) d) (many (Nat) q p c o) (erased (Lt q B40) bq) (erased (Lt p B40) bp) (erased (Lt c B40) bc)
    (erased (Lt o B40) bo) -> (many (ACN) a) (erased (PlaceN d q p c o a) pl) (erased (BdA a) ba))
  (match many d _
    ((DL) (values (MkACN q p c o) (PNL q p c o) (MkBdA q p c o bq bp bc bo)))
    ((DR) (values (MkACN q o c p) (PNR q p c o) (MkBdA q o c p bq bo bc bp)))))

(def-fns _ $ (many all-from : (many (List (ACN)) S) (many (AV (ACN) S) SA) (many (Dir) d) (many (Nat) q o) (subterm many (List (Pair (Nat) (Nat))) row)
    (many (List (Nat)) tg) (erased (All (ACN) BdA S) bS) (erased (Lt q B40) bq) (erased (Lt o B40) bo)
    (erased (All (Pair (Nat) (Nat)) BdP row) br) -> (many (Res (AllFrom S d q o row)) r))
  (let-match many row (Cons _ e rest) ((Nil _) (ROk _ (AFNil S d q o))))
  (let-match many tg (Cons _ j tgr) ((Nil _) (RFail _)))
  (let-match erased br (AllCons _ _ _ _ be br1))
  (let-match many e (MkPair _ _ c s2))
  (let-match erased be (MkBdP _ _ pc p2))
  (let ((many a) (erased pl) (erased ba)) (place-n d q s2 c o bq p2 pc bo))
  (let-match many (aget _ _ SA j) (NOk _ _ _ x nx) ((NNo _ _ _) (RFail _)))
  (let-match many (eq-acn a x ba (all-nth (ACN) BdA S j x bS nx)) (Some _ ex) ((None _) (RFail _)))
  (let-match many ex (Refl _ _))
  (let-match many (notail $ all-from S SA d q o rest tgr bS bq bo br1) (ROk _ af) ((RFail _) (RFail _)))
  (ROk _ (AFHit S d q o c s2 rest a pl (nth-mem (ACN) S j a nx) af)))

(def-fns _ $ (many edge-in : (many (List (List (Pair (Nat) (Nat)))) adj) (many (AV (List (Pair (Nat) (Nat))) adj) AA) (many (Nat) s c s2) (erased (All (List (Pair (Nat) (Nat))) BdRow adj) badj)
    (erased (Lt c B40) pc) (erased (Lt s2 B40) p2) -> (many (Res (EIn adj s c s2)) r))
  (let-match many (aget _ _ AA s) (NOk _ _ _ row nr) ((NNo _ _ _) (RFail _)))
  (let-match erased (all-nth (List (Pair (Nat) (Nat))) BdRow adj s row badj nr) (MkBdRow _ br))
  (let-match many (find-pair c s2 row pc p2 br) (ROk _ mr) ((RFail _) (RFail _)))
  (ROk _ (MkEIn adj s c s2 row nr mr)))

(def-adts
  ((SidesR : ((List (List (Pair (Nat) (Nat)))) adj) ((List (ACN)) S) ((Dir) d) ((Nat) q2) ((Nat) o2) ((Nat) cn) ((Nat) sp) ((Nat) so) -> Type)
    enum
    (many SOk : (erased (List (List (Pair (Nat) (Nat)))) adj) (erased (List (ACN)) S) (erased (Dir) d) (erased (Nat) q2 o2 cn sp so) (erased (List (Pair (Nat) (Nat))) row)
       (erased (EIn adj o2 cn so) me) (erased (Nth (List (Pair (Nat) (Nat))) adj sp row) nr) (erased (AllFrom S d q2 o2 row) af) -> (SidesR adj S d q2 o2 cn sp so))
    (many SNo : (erased (List (List (Pair (Nat) (Nat)))) adj) (erased (List (ACN)) S) (erased (Dir) d) (erased (Nat) q2 o2 cn sp so) -> (SidesR adj S d q2 o2 cn sp so))))

(def-fns _ $ (many sides : (many (List (List (Pair (Nat) (Nat)))) adj) (many (AV (List (Pair (Nat) (Nat))) adj) AA) (many (List (ACN)) S) (many (AV (ACN) S) SA) (many (Dir) d)
    (many (Nat) q2 o2 cn sp so) (many (List (Nat)) tg) (erased (All (ACN) BdA S) bS) (erased (All (List (Pair (Nat) (Nat))) BdRow adj) badj)
    (erased (Lt q2 B40) bq2) (erased (Lt o2 B40) bo2) (erased (Lt cn B40) bcn) (erased (Lt sp B40) bp) (erased (Lt so B40) bo) ->
    (many (SidesR adj S d q2 o2 cn sp so) r))
  (let-match many (edge-in adj AA o2 cn so badj bcn bo) (ROk _ me) ((RFail _) (SNo adj S d q2 o2 cn sp so)))
  (let-match many (aget _ _ AA sp) (NOk _ _ _ row nr) ((NNo _ _ _) (SNo adj S d q2 o2 cn sp so)))
  (let-match erased (all-nth (List (Pair (Nat) (Nat))) BdRow adj sp row badj nr) (MkBdRow _ brow))
  (let-match many (all-from S SA d q2 o2 row tg bS bq2 bo2 brow) (ROk _ af) ((RFail _) (SNo adj S d q2 o2 cn sp so)))
  (SOk adj S d q2 o2 cn sp so row me nr af))

(def-fns _ $ (many aokn : (many (List (PT)) p) (many (List (Bool)) sy) (many (AV (Bool) sy) SY) (many (List (List (Pair (Nat) (Nat)))) adj) (many (AV (List (Pair (Nat) (Nat))) adj) AA)
    (many (List (ACN)) S) (many (AV (ACN) S) SA) (many (ACN) a) (many (Choice) ch) (erased (All (ACN) BdA S) bS)
    (erased (All (List (Pair (Nat) (Nat))) BdRow adj) badj) (erased (BdA a) ba) (erased (BdC ch) bc) -> (many (Res (AOKN p sy adj S a)) r))
  (let-match many a (MkACN q sl sh sr))
  (let-match erased ba (MkBdA _ _ _ _ _ bl _ br))
  (let-match many ch (MkCh cn o2 tg))
  (let-match erased bc (MkBdC _ _ _ bcn bo2))
  (let-match many (aget _ _ SY sh) (NOk _ _ _ h nh) ((NNo _ _ _) (RFail _)))
  (let-match many (plook p q h) (PLOk _ _ _ x pl) ((PLNo _ _ _) (RFail _)))
  (let-match many x (Def t) ((Undef) (RFail _)))
  (let-match many t (Go w d q2) ((Halt) (RFail _)))
  (let-match many (bd q2) (ROk _ bq2) ((RFail _) (RFail _)))
  (let-match many (aget _ _ SY cn) (NOk _ _ _ w2 nw) ((NNo _ _ _) (RFail _)))
  (let-match many (eq-bit w2 w) (Some _ ew) ((None _) (RFail _)))
  (let-match many ew (Refl _ _))
  (match many d _
    ((DL)
      (let-match many (sides adj AA S SA (DL) q2 o2 cn sl sr tg bS badj bq2 bo2 bcn bl br) (SOk _ _ _ _ _ _ _ _ row me nr af) ((SNo _ _ _ _ _ _ _ _) (RFail _)))
      (ROk _ (AKL p sy adj S q sl sh sr q2 cn o2 h w pl nh nw row me nr af)))
    ((DR)
      (let-match many (sides adj AA S SA (DR) q2 o2 cn sr sl tg bS badj bq2 bo2 bcn br bl) (SOk _ _ _ _ _ _ _ _ row me nr af) ((SNo _ _ _ _ _ _ _ _) (RFail _)))
      (ROk _ (AKR p sy adj S q sl sh sr q2 cn o2 h w pl nh nw row me nr af)))))

(def-fns _ $ (many closedn : (many (List (PT)) p) (many (List (Bool)) sy) (many (AV (Bool) sy) SY) (many (List (List (Pair (Nat) (Nat)))) adj) (many (AV (List (Pair (Nat) (Nat))) adj) AA)
    (many (List (ACN)) S) (many (AV (ACN) S) SA) (subterm many (List (ACN)) T) (many (List (Choice)) ch)
    (erased (All (ACN) BdA S) bS) (erased (All (List (Pair (Nat) (Nat))) BdRow adj) badj) (erased (All (ACN) BdA T) bT) (erased (All (Choice) BdC ch) bch) ->
    (many (Res (ClosedN p sy adj S T)) r))
  (let-match many T (Cons _ a rest) ((Nil _) (ROk _ (CNNil p sy adj S))))
  (let-match erased bT (AllCons _ _ _ _ ba bT1))
  (let-match many ch (Cons _ c crest) ((Nil _) (RFail _)))
  (let-match erased bch (AllCons _ _ _ _ bc bch1))
  (let-match many (aokn p sy SY adj AA S SA a c bS badj ba bc) (ROk _ ok) ((RFail _) (RFail _)))
  (let-match many (notail $ closedn p sy SY adj AA S SA rest crest bS badj bT1 bch1) (ROk _ cl) ((RFail _) (RFail _)))
  (ROk _ (CNCons p sy adj S rest a ok cl)))

(def-adts
  ((BlankR : ((List (Bool)) sy) ((List (Pair (Nat) (Nat))) row) ((List (Nat)) acc) -> Type)
    enum
    (many BOk : (erased (List (Bool)) sy) (erased (List (Pair (Nat) (Nat))) row) (erased (List (Nat)) acc) (many (Nat) c a2)
       (erased (Mem (Pair (Nat) (Nat)) (MkPair (Nat) (Nat) c a2) row) mr) (erased (Nth (Bool) sy c (BFalse)) nb) (erased (Mem (Nat) a2 acc) ma)
       -> (BlankR sy row acc))
    (many BNo : (erased (List (Bool)) sy) (erased (List (Pair (Nat) (Nat))) row) (erased (List (Nat)) acc) -> (BlankR sy row acc))))

(def-fns _ $ (many blank-row : (many (List (Bool)) sy) (many (AV (Bool) sy) SY) (many (List (Nat)) acc) (subterm many (List (Pair (Nat) (Nat))) row)
    (erased (All (Nat) BdN acc) bacc) (erased (All (Pair (Nat) (Nat)) BdP row) br) -> (many (BlankR sy row acc) r))
  (let-match many row (Cons _ e rest) ((Nil _) (BNo sy row acc)))
  (let-match erased br (AllCons _ _ _ _ be br1))
  (let-match many e (MkPair _ _ c a2))
  (let-match erased be (MkBdP _ _ _ p2))
  (let ((many next))
    (match many (notail $ blank-row sy SY acc rest bacc br1) (((BlankR sy row acc) x))
      ((BOk _ _ _ c3 a3 mr nb ma) (BOk sy row acc c3 a3 (MemThere _ _ e rest mr) nb ma))
      ((BNo _ _ _) (BNo sy row acc))))
  (let-match many (aget _ _ SY c) (NOk _ _ _ b nb) ((NNo _ _ _) next))
  (let-match many b (BFalse) ((BTrue) next))
  (let-match many (find-nat a2 acc p2 bacc) (ROk _ ma) ((RFail _) next))
  (BOk sy row acc c a2 (MemHere _ _ rest) nb ma))

(def-fns _ $ (many acc-all : (many (List (Bool)) sy) (many (AV (Bool) sy) SY) (many (List (List (Pair (Nat) (Nat)))) adj) (many (AV (List (Pair (Nat) (Nat))) adj) AA) (many (List (Nat)) acc)
    (subterm many (List (Nat)) as) (erased (All (List (Pair (Nat) (Nat))) BdRow adj) badj) (erased (All (Nat) BdN acc) bacc) (erased (All (Nat) BdN as) bas) ->
    (many (Res (AccAll sy adj acc as)) r))
  (let-match many as (Cons _ a rest) ((Nil _) (ROk _ (AANil sy adj acc))))
  (let-match erased bas (AllCons _ _ _ _ _ bas1))
  (let-match many (aget _ _ AA a) (NOk _ _ _ row nr) ((NNo _ _ _) (RFail _)))
  (let-match erased (all-nth (List (Pair (Nat) (Nat))) BdRow adj a row badj nr) (MkBdRow _ br))
  (let-match many (blank-row sy SY acc row bacc br) (BOk _ _ _ c a2 mr nb ma) ((BNo _ _ _) (RFail _)))
  (let-match many (notail $ acc-all sy SY adj AA acc rest badj bacc bas1) (ROk _ aa) ((RFail _) (RFail _)))
  (ROk _ (AACons sy adj acc rest a c a2 (MkEIn adj a c a2 row nr mr) nb ma aa)))

(def-fns _ $ (many check-cert : (many (Nat) n k) (many (List (PT)) p) (many (Cert) ct) -> (many (Res (TNode n k p)) r))
  (let-match many ct (MkCert sy adj acc S ch a0))
  (let-match many (bd-acns (Cons (ACN) a0 S)) (ROk _ bS0) ((RFail _) (RFail _)))
  (let-match erased bS0 (AllCons _ _ _ _ ba0 bS))
  (let-match many (bd-rows adj) (ROk _ badj) ((RFail _) (RFail _)))
  (let-match many (bd-nats acc) (ROk _ bacc) ((RFail _) (RFail _)))
  (let-match many (bd-chs ch) (ROk _ bch) ((RFail _) (RFail _)))
  (let ((many SY)) (mk-av _ sy))
  (let ((many AA)) (mk-av _ adj))
  (let ((many SA)) (mk-av _ S))
  (let-match many (closedn p sy SY adj AA S SA S ch bS badj bS bch) (ROk _ cl) ((RFail _) (RFail _)))
  (let-match many (acc-all sy SY adj AA acc acc badj bacc bacc) (ROk _ aa) ((RFail _) (RFail _)))
  (let-match many (find-acn a0 S ba0 bS) (ROk _ ma) ((RFail _) (RFail _)))
  (let-match many a0 (MkACN q0 sl sh sr))
  (let-match erased ba0 (MkBdA _ _ _ _ _ bl _ br))
  (let-match many q0 (Zero) ((Succ _) (RFail _)))
  (let-match many (aget _ _ SY sh) (NOk _ _ _ h nh) ((NNo _ _ _) (RFail _)))
  (let-match many h (BFalse) ((BTrue) (RFail _)))
  (let-match many (find-nat sl acc bl bacc) (ROk _ ml) ((RFail _) (RFail _)))
  (let-match many (find-nat sr acc br bacc) (ROk _ mr) ((RFail _) (RFail _)))
  (ROk _ (TN n k p sy adj acc S cl aa a0 ma
    (MkGCN sy adj acc (Zero) sl sh sr (Nil (Bool)) (Nil (Bool)) (BFalse) (GAcc sy adj acc sl ml) (GAcc sy adj acc sr mr) nh))))

(def-adts
  ((DefL : ((List (Tr)) m) ((List (PT)) p) -> Type)
    enum
    (many DLNil : -> (DefL (Nil (Tr)) (Nil (PT))))
    (many DLCons : (erased (Tr) t) (erased (List (Tr)) m) (erased (List (PT)) p) (erased (DefL m p) d) -> (DefL (Cons (Tr) t m) (Cons (PT) (Def t) p)))))

(def-fns _ $ (many defs : (subterm many (List (Tr)) m) -> (many (List (PT)) p) (erased (DefL m p) d))
  (let-match many m (Cons _ t rest) ((Nil _) (values (Nil (PT)) (DLNil))))
  (let ((many p) (erased d)) (notail $ defs rest))
  (values (Cons (PT) (Def t) p) (DLCons t rest p d)))

(def-fns _ $ (erased defl-ext : (erased (List (Tr)) m) (erased (List (PT)) p) (subterm erased (DefL m p) d) -> (erased (Ext p m) e))
  (match erased d _
    ((DLNil) (ExNil))
    ((DLCons t rest p1 d1) (ExD t p1 rest (defl-ext rest p1 d1)))))

(def-fns _ $ (erased swap0 : (erased (Nat) q) -> (erased (Swap (Zero) (Zero) q q) s))
  (let-match erased q (Succ q1) ((Zero) (SwA (Zero) (Zero))))
  (let ((erased ap)) (ApLt (Nat) Lt (Zero) q (LtZ q1)))
  (SwO (Zero) (Zero) q ap ap))

(def-fns _ $ (many flip-p : (subterm many (List (PT)) p) -> (many (List (PT)) p2) (erased (XP p p2) x))
  (let-match many p (Cons _ y rest) ((Nil _) (values (Nil (PT)) (XPNil))))
  (let ((many rest2) (erased x)) (notail $ flip-p rest))
  (let-match many y (Def t) ((Undef) (values (Cons (PT) (Undef) rest2) (XPU rest rest2 x))))
  (let-match many t (Go w d q) ((Halt) (values (Cons (PT) y rest2) (XPD t t rest rest2 (XTH (BTrue) (Zero) (Zero)) x))))
  (let ((many e) (erased fl)) (match many d (((Dir) e) ((Flip (BTrue) d e) fl)) ((DL) (values (DR) (FlL))) ((DR) (values (DL) (FlR)))))
  (values (Cons (PT) (Def (Go w e q)) rest2) (XPD t (Go w e q) rest rest2 (XTG (BTrue) (Zero) (Zero) w d e q q fl (swap0 q)) x)))

(def-adts
  ((LSimR : ((List (PT)) p) ((Cfg) c) ((Nat) t) -> Type)
    enum
    (many LSOk : (erased (List (PT)) p) (erased (Cfg) c) (erased (Nat) t) (many (Nat) q) (many (List (Bool)) l) (many (Bool) h) (many (List (Bool)) r)
       (erased (LRun p c t (MkCfg q l h r)) lr) -> (LSimR p c t))
    (many LSNo : (erased (List (PT)) p) (erased (Cfg) c) (erased (Nat) t) -> (LSimR p c t))))

(def-fns _ $ (many pop : (many (List (Bool)) r) -> (many (Bool) h) (many (List (Bool)) r2) (erased (Pop r h r2) pp))
  (match many r _ ((Nil _) (values (BFalse) r (PopNil))) ((Cons _ h r2) (values h r2 (PopCons h r2)))))

(def-fns _ $ (many lsim : (many (List (PT)) p) (subterm many (Nat) t) (many (Nat) q) (many (List (Bool)) l) (many (Bool) h) (many (List (Bool)) r)
    -> (many (LSimR p (MkCfg q l h r) t) res))
  (let ((many no)) (LSNo p (MkCfg q l h r) t))
  (let-match many t (Succ t1) ((Zero) (LSOk p _ t q l h r (LRNil p _))))
  (let-match many (plook p q h) (PLOk _ _ _ x pl) ((PLNo _ _ _) no))
  (let-match many x (Def tr) ((Undef) no))
  (let-match many tr (Go w d q2) ((Halt) no))
  (match many d _
    ((DL)
      (let-match many l (Cons _ h2 l2) ((Nil _) no))
      (let-match many (notail $ lsim p t1 q2 l2 h2 (Cons (Bool) w r)) (LSOk _ _ _ qe le he re lr) ((LSNo _ _ _) no))
      (LSOk p _ t qe le he re (LRCons p _ _ _ t1 (LStepL p q q2 l2 r h w h2 pl) lr)))
    ((DR)
      (let ((many h2) (many r2) (erased pp)) (pop r))
      (let-match many (notail $ lsim p t1 q2 (Cons (Bool) w l) h2 r2) (LSOk _ _ _ qe le he re lr) ((LSNo _ _ _) no))
      (LSOk p _ t qe le he re (LRCons p _ _ _ t1 (LStepR p q q2 l r r2 h w h2 pl pp) lr)))))

(def-adts
  ((Spl : ((List (Bool)) zs) -> Type)
    enum
    (many MkSpl : (erased (List (Bool)) zs) (many (List (Bool)) xs ys) (erased (Cat (Bool) xs ys zs) c) -> (Spl zs))
    (many NoSpl : (erased (List (Bool)) zs) -> (Spl zs))))

(def-fns _ $ (many split-at : (subterm many (Nat) n) (many (List (Bool)) zs) -> (many (Spl zs) r))
  (let-match many n (Succ n1) ((Zero) (MkSpl zs (Nil (Bool)) zs (CatN (Bool) zs))))
  (let-match many zs (Cons _ z rest) ((Nil _) (NoSpl zs)))
  (let-match many (notail $ split-at n1 rest) (MkSpl _ xs ys c) ((NoSpl _) (NoSpl zs)))
  (MkSpl zs (Cons (Bool) z xs) ys (CatC (Bool) z xs ys rest c)))

(def-fns _ $ (many eq-bools : (subterm many (List (Bool)) xs) (many (List (Bool)) ys) -> (many (Maybe (Eq (List (Bool)) xs ys)) r))
  (let-match many xs (Cons _ x xr)
    ((Nil _) (match many ys _ ((Nil _) (Some _ (Refl (List (Bool)) xs))) ((Cons _ _ _) (None _)))))
  (let-match many ys (Cons _ y yr) ((Nil _) (None _)))
  (let-match many (eq-bit x y) (Some _ e) ((None _) (None _)))
  (let-match erased e (Refl _ _))
  (let-match many (notail $ eq-bools xr yr) (Some _ e2) ((None _) (None _)))
  (let-match erased e2 (Refl _ _))
  (Some _ (Refl (List (Bool)) xs)))

(def-fns _ $ (many check-cyc : (many (Nat) n k) (many (List (PT)) p) (many (Bool) f) (many (Nat) t1 D P) -> (many (Res (TNode n k p)) res))
  (let ((many p2) (erased mi))
    (match many f (((List (PT)) p2) ((Mir f p p2) mi))
      ((BFalse) (values p (MirN p)))
      ((BTrue) (let ((many p3) (erased xp)) (flip-p p)) (values p3 (MirY p p3 xp)))))
  (let-match many (psim p2 t1 (Zero) (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)) (PRNil p2 _)) (PSOut _ t q l r h pr)
    (else (RFail _)))
  (let-match many (split-at D l) (MkSpl _ x y c) ((NoSpl _) (RFail _)))
  (let-match many P (Succ T) ((Zero) (RFail _)))
  (let-match many (lsim p2 P q x h r) (LSOk _ _ _ qe x2 he re lr) ((LSNo _ _ _) (RFail _)))
  (let-match many (eq-nat qe q) (Some _ e1) ((None _) (RFail _)))
  (let-match erased e1 (Refl _ _))
  (let-match many (eq-bit he h) (Some _ e2) ((None _) (RFail _)))
  (let-match erased e2 (Refl _ _))
  (let-match many (eq-bools re r) (Some _ e3) ((None _) (RFail _)))
  (let-match erased e3 (Refl _ _))
  (let-match many (split-at D x2) (MkSpl _ x3 w cw) ((NoSpl _) (RFail _)))
  (let-match many (eq-bools x3 x) (Some _ e4) ((None _) (RFail _)))
  (let-match erased e4 (Refl _ _))
  (ROk _ (TC n k p p2 f mi (MkCyc p2 t T q x w x2 r y l h pr c lr cw))))
