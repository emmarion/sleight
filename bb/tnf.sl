
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
    (many PSOut : (erased (List (PT)) p) -> (PSimR p))))

(def-fns _ $ (many psim : (many (List (PT)) p) (subterm many (Nat) fuel) (many (Nat) t q) (many (List (Bool)) l) (many (Bool) h) (many (List (Bool)) r)
    (erased (PRunTo p (MkCfg (Zero) (Nil (Bool)) (BFalse) (Nil (Bool))) t (MkCfg q l h r)) pr) -> (many (PSimR p) res))
  (let-match many fuel (Succ f) ((Zero) (PSOut p)))
  (let-match many (plook p q h) (PLOk _ _ _ x pl) ((PLNo _ _ _) (PSOut p)))
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

(def-adts $ (Cert : -> Type)
  enum
  (many MkCert : (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (Nat)) acc) (many (List (ACN)) S)
     (many (List (Pair (Nat) (Nat))) ch) (many (ACN) a0) -> (Cert)))

(def-adts
  ((NthR : (Type A) ((List A) xs) ((Nat) i) -> Type)
    enum
    (many NOk : (erased Type A) (erased (List A) xs) (erased (Nat) i) (many A x) (erased (Nth A xs i x) p) -> (NthR A xs i))
    (many NNo : (erased Type A) (erased (List A) xs) (erased (Nat) i) -> (NthR A xs i))))

(def-fns _ $ (many nth-r : (erased Type A) (subterm many (List A) xs) (many (Nat) i) -> (many (NthR A xs i) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (NNo A xs i)))
  (match many i _
    ((Zero) (NOk A xs i x (NthHere A x rest)))
    ((Succ i1)
      (let-match many (notail $ nth-r A rest i1) (NOk _ _ _ y p) ((NNo _ _ _) (NNo A xs i)))
      (NOk A xs i y (NthThere A x rest i1 y p)))))

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
  ((BdE : ((Edge) e) -> Type)
    enum
    (many MkBdE : (erased (Nat) s c s2) (erased (Lt s B40) a) (erased (Lt c B40) b) (erased (Lt s2 B40) d) -> (BdE (MkE s c s2)))))

(def-adts
  ((BdP : ((Pair (Nat) (Nat)) c) -> Type)
    enum
    (many MkBdP : (erased (Nat) a b) (erased (Lt a B40) pa) (erased (Lt b B40) pb) -> (BdP (MkPair (Nat) (Nat) a b)))))

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

(def-fns _ $ (many bd-edges : (subterm many (List (Edge)) xs) -> (many (Res (All (Edge) BdE xs)) r))
  (let-match many xs (Cons _ e rest) ((Nil _) (ROk _ (AllNil (Edge) BdE))))
  (let-match many e (MkE s c s2))
  (let-match many (bd s) (ROk _ ps) ((RFail _) (RFail _)))
  (let-match many (bd c) (ROk _ pc) ((RFail _) (RFail _)))
  (let-match many (bd s2) (ROk _ p2) ((RFail _) (RFail _)))
  (let-match many (notail $ bd-edges rest) (ROk _ r) ((RFail _) (RFail _)))
  (ROk _ (AllCons (Edge) BdE e rest (MkBdE s c s2 ps pc p2) r)))

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

(def-fns _ $ (many eq-edge : (many (Edge) x) (many (Edge) y) (erased (BdE x) bx) (erased (BdE y) by) -> (many (Maybe (Eq (Edge) x y)) r))
  (let-match many x (MkE a1 b1 c1))
  (let-match many y (MkE a2 b2 c2))
  (let-match erased bx (MkBdE _ _ _ pa1 pb1 pc1))
  (let-match erased by (MkBdE _ _ _ pa2 pb2 pc2))
  (let-match many (beq a1 a2 pa1 pa2) (Equal _ _ _) (else (None _)))
  (let-match many (beq b1 b2 pb1 pb2) (Equal _ _ _) (else (None _)))
  (let-match many (beq c1 c2 pc1 pc2) (Equal _ _ _) (else (None _)))
  (Some _ (Refl (Edge) x)))

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

(def-fns _ $ (many find-edge : (many (Edge) a) (subterm many (List (Edge)) xs) (erased (BdE a) ba) (erased (All (Edge) BdE xs) bs) ->
    (many (Res (Mem (Edge) a xs)) r))
  (let-match many xs (Cons _ b rest) ((Nil _) (RFail _)))
  (let-match erased bs (AllCons _ _ _ _ bb bs1))
  (match many (eq-edge a b ba bb) _
    ((Some _ e) (let-match many e (Refl _ _)) (ROk _ (MemHere (Edge) a rest)))
    ((None _)
      (let-match many (notail $ find-edge a rest ba bs1) (ROk _ mm) ((RFail _) (RFail _)))
      (ROk _ (MemThere (Edge) a b rest mm)))))

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

(def-fns _ $ (many all-from : (many (List (ACN)) S) (many (Dir) d) (many (Nat) q o s) (subterm many (List (Edge)) es)
    (erased (All (ACN) BdA S) bS) (erased (Lt q B40) bq) (erased (Lt o B40) bo) (erased (Lt s B40) bs) (erased (All (Edge) BdE es) be) ->
    (many (Res (AllFrom S d q o es s)) r))
  (let-match many es (Cons _ e rest) ((Nil _) (ROk _ (AFNil S d q o s))))
  (let-match erased be (AllCons _ _ _ _ b1 be1))
  (let-match many e (MkE s1 c s2))
  (let-match erased b1 (MkBdE _ _ _ p1 pc p2))
  (let-match many (notail $ all-from S d q o s rest bS bq bo bs be1) (ROk _ af) ((RFail _) (RFail _)))
  (match many (beq s1 s p1 bs) _
    ((Equal _ _ _)
      (let ((many a) (erased pl) (erased ba)) (place-n d q s2 c o bq p2 pc bo))
      (let-match many (find-acn a S ba bS) (ROk _ ma) ((RFail _) (RFail _)))
      (ROk _ (AFHit S d q o s c s2 rest a pl ma af)))
    ((Unequal _ _ _ _ ap) (ROk _ (AFSkip S d q o s s1 c s2 rest ap af)))))

(def-fns _ $ (many aokn : (many (List (PT)) p) (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (ACN)) S)
    (many (ACN) a) (many (Nat) cn o2) (erased (All (ACN) BdA S) bS) (erased (All (Edge) BdE es) be) (erased (BdA a) ba)
    (erased (Lt cn B40) bc) (erased (Lt o2 B40) bo) -> (many (Res (AOKN p sy es S a)) r))
  (let-match many a (MkACN q sl sh sr))
  (let-match erased ba (MkBdA _ _ _ _ _ bl _ br))
  (let-match many (nth-r _ sy sh) (NOk _ _ _ h nh) ((NNo _ _ _) (RFail _)))
  (let-match many (plook p q h) (PLOk _ _ _ x pl) ((PLNo _ _ _) (RFail _)))
  (let-match many x (Def t) ((Undef) (RFail _)))
  (let-match many t (Go w d q2) ((Halt) (RFail _)))
  (let-match many (bd q2) (ROk _ bq2) ((RFail _) (RFail _)))
  (let-match many (nth-r _ sy cn) (NOk _ _ _ w2 nw) ((NNo _ _ _) (RFail _)))
  (let-match many (eq-bit w2 w) (Some _ ew) ((None _) (RFail _)))
  (let-match many ew (Refl _ _))
  (match many d _
    ((DL)
      (let-match many (find-edge (MkE o2 cn sr) es (MkBdE o2 cn sr bo bc br) be) (ROk _ me) ((RFail _) (RFail _)))
      (let-match many (all-from S (DL) q2 o2 sl es bS bq2 bo bl be) (ROk _ af) ((RFail _) (RFail _)))
      (ROk _ (AKL p sy es S q sl sh sr q2 cn o2 h w pl nh nw me af)))
    ((DR)
      (let-match many (find-edge (MkE o2 cn sl) es (MkBdE o2 cn sl bo bc bl) be) (ROk _ me) ((RFail _) (RFail _)))
      (let-match many (all-from S (DR) q2 o2 sr es bS bq2 bo br be) (ROk _ af) ((RFail _) (RFail _)))
      (ROk _ (AKR p sy es S q sl sh sr q2 cn o2 h w pl nh nw me af)))))

(def-fns _ $ (many closedn : (many (List (PT)) p) (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (ACN)) S)
    (subterm many (List (ACN)) T) (many (List (Pair (Nat) (Nat))) ch) (erased (All (ACN) BdA S) bS) (erased (All (Edge) BdE es) be)
    (erased (All (ACN) BdA T) bT) (erased (All (Pair (Nat) (Nat)) BdP ch) bch) -> (many (Res (ClosedN p sy es S T)) r))
  (let-match many T (Cons _ a rest) ((Nil _) (ROk _ (CNNil p sy es S))))
  (let-match erased bT (AllCons _ _ _ _ ba bT1))
  (let-match many ch (Cons _ c crest) ((Nil _) (RFail _)))
  (let-match erased bch (AllCons _ _ _ _ bc bch1))
  (let-match many c (MkPair _ _ cn o2))
  (let-match erased bc (MkBdP _ _ bcn bo2))
  (let-match many (aokn p sy es S a cn o2 bS be ba bcn bo2) (ROk _ ok) ((RFail _) (RFail _)))
  (let-match many (notail $ closedn p sy es S rest crest bS be bT1 bch1) (ROk _ cl) ((RFail _) (RFail _)))
  (ROk _ (CNCons p sy es S rest a ok cl)))

(def-adts
  ((BlankR : ((List (Bool)) sy) ((List (Edge)) es) ((List (Nat)) acc) ((Nat) a) -> Type)
    enum
    (many BOk : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (Nat) a) (many (Nat) c a2)
       (erased (Mem (Edge) (MkE a c a2) es) me) (erased (Nth (Bool) sy c (BFalse)) nb) (erased (Mem (Nat) a2 acc) ma) -> (BlankR sy es acc a))
    (many BNo : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (Nat) a) -> (BlankR sy es acc a))))

(def-fns _ $ (many blank-from : (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (Nat)) acc) (many (Nat) a)
    (subterm many (List (Edge)) es0) (erased (All (Edge) BdE es) be) (erased (All (Nat) BdN acc) bacc) (erased (Lt a B40) pa)
    (erased (All (Edge) BdE es0) be0) -> (many (BlankR sy es acc a) r))
  (let-match many es0 (Cons _ e rest) ((Nil _) (BNo sy es acc a)))
  (let-match erased be0 (AllCons _ _ _ _ b1 be1))
  (let-match many e (MkE s c a2))
  (let-match erased b1 (MkBdE _ _ _ ps pc p2))
  (let ((many next)) (notail $ blank-from sy es acc a rest be bacc pa be1))
  (let-match many (beq s a ps pa) (Equal _ _ _) (else next))
  (let-match many (nth-r _ sy c) (NOk _ _ _ b nb) ((NNo _ _ _) next))
  (let-match many b (BFalse) ((BTrue) next))
  (let-match many (find-nat a2 acc p2 bacc) (ROk _ ma) ((RFail _) next))
  (let-match many (find-edge (MkE a c a2) es (MkBdE a c a2 pa pc p2) be) (ROk _ me) ((RFail _) next))
  (BOk sy es acc a c a2 me nb ma))

(def-fns _ $ (many acc-all : (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (Nat)) acc) (subterm many (List (Nat)) as)
    (erased (All (Edge) BdE es) be) (erased (All (Nat) BdN acc) bacc) (erased (All (Nat) BdN as) bas) -> (many (Res (AccAll sy es acc as)) r))
  (let-match many as (Cons _ a rest) ((Nil _) (ROk _ (AANil sy es acc))))
  (let-match erased bas (AllCons _ _ _ _ ba bas1))
  (let-match erased ba (MkBdN _ pa))
  (let-match many (blank-from sy es acc a es be bacc pa be) (BOk _ _ _ _ c a2 me nb ma) ((BNo _ _ _ _) (RFail _)))
  (let-match many (notail $ acc-all sy es acc rest be bacc bas1) (ROk _ aa) ((RFail _) (RFail _)))
  (ROk _ (AACons sy es acc rest a c a2 me nb ma aa)))

(def-fns _ $ (many check-cert : (many (Nat) n k) (many (List (PT)) p) (many (Cert) ct) -> (many (Res (TNode n k p)) r))
  (let-match many ct (MkCert sy es acc S ch a0))
  (let-match many (bd-acns (Cons (ACN) a0 S)) (ROk _ bS0) ((RFail _) (RFail _)))
  (let-match erased bS0 (AllCons _ _ _ _ ba0 bS))
  (let-match many (bd-edges es) (ROk _ be) ((RFail _) (RFail _)))
  (let-match many (bd-nats acc) (ROk _ bacc) ((RFail _) (RFail _)))
  (let-match many (bd-pairs ch) (ROk _ bch) ((RFail _) (RFail _)))
  (let-match many (closedn p sy es S S ch bS be bS bch) (ROk _ cl) ((RFail _) (RFail _)))
  (let-match many (acc-all sy es acc acc be bacc bacc) (ROk _ aa) ((RFail _) (RFail _)))
  (let-match many (find-acn a0 S ba0 bS) (ROk _ ma) ((RFail _) (RFail _)))
  (let-match many a0 (MkACN q0 sl sh sr))
  (let-match erased ba0 (MkBdA _ _ _ _ _ bl _ br))
  (let-match many q0 (Zero) ((Succ _) (RFail _)))
  (let-match many (nth-r _ sy sh) (NOk _ _ _ h nh) ((NNo _ _ _) (RFail _)))
  (let-match many h (BFalse) ((BTrue) (RFail _)))
  (let-match many (find-nat sl acc bl bacc) (ROk _ ml) ((RFail _) (RFail _)))
  (let-match many (find-nat sr acc br bacc) (ROk _ mr) ((RFail _) (RFail _)))
  (ROk _ (TN n k p sy es acc S cl aa a0 ma
    (MkGCN sy es acc (Zero) sl sh sr (Nil (Bool)) (Nil (Bool)) (BFalse) (GAcc sy es acc sl ml) (GAcc sy es acc sr mr) nh))))

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
