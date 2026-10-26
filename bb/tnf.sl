
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

(def-fns _ $ (many skip-ws : (subterm many (Nat) fuel) (many (String) s) -> (many (String) r))
  (let-match many fuel (Succ f) ((Zero) s))
  (let-match many s (SCons c rest) ((SNil) s))
  (match many (get-dig c) _
    ((GotOk _ _ _ _ _) s)
    ((GotNo _ _ _) (tail $ skip-ws f rest))))

(def-fns _ $ (many rd-digits : (subterm many (Nat) fuel) (many (String) s) (many (Nat) acc) -> (many (Nat) n) (many (String) r))
  (let-match many fuel (Succ f) ((Zero) (values acc s)))
  (let-match many s (SCons c rest) ((SNil) (values acc s)))
  (match many (get-dig c) _
    ((GotOk _ _ _ d _) (let ((many x) (erased _)) (mul acc 10)) (let ((many a2) (erased _)) (add x d)) (tail $ rd-digits f rest a2))
    ((GotNo _ _ _) (values acc s))))

(def-fns _ $ (many next-nat : (many (String) s) -> (many (Nat) n) (many (String) r))
  (tail $ rd-digits 20 (skip-ws 100 s) 0))

(def-fns _ $ (many rd-bools : (subterm many (Nat) k) (many (String) s) -> (many (List (Bool)) xs) (many (String) r))
  (let-match many k (Succ k1) ((Zero) (values (Nil (Bool)) s)))
  (let ((many v) (many s1)) (next-nat s))
  (let ((many rest) (many s2)) (notail $ rd-bools k1 s1))
  (match many v _ ((Zero) (values (Cons (Bool) (BFalse) rest) s2)) (else (values (Cons (Bool) (BTrue) rest) s2))))

(def-fns _ $ (many rd-nats : (subterm many (Nat) k) (many (String) s) -> (many (List (Nat)) xs) (many (String) r))
  (let-match many k (Succ k1) ((Zero) (values (Nil (Nat)) s)))
  (let ((many v) (many s1)) (next-nat s))
  (let ((many rest) (many s2)) (notail $ rd-nats k1 s1))
  (values (Cons (Nat) v rest) s2))

(def-fns _ $ (many rd-edges : (subterm many (Nat) k) (many (String) s) -> (many (List (Edge)) xs) (many (String) r))
  (let-match many k (Succ k1) ((Zero) (values (Nil (Edge)) s)))
  (let ((many a) (many s1)) (next-nat s))
  (let ((many c) (many s2)) (next-nat s1))
  (let ((many b) (many s3)) (next-nat s2))
  (let ((many rest) (many s4)) (notail $ rd-edges k1 s3))
  (values (Cons (Edge) (MkE a c b) rest) s4))

(def-fns _ $ (many rd-acn : (many (String) s) -> (many (ACN) a) (many (String) r))
  (let ((many q) (many s1)) (next-nat s))
  (let ((many sl) (many s2)) (next-nat s1))
  (let ((many sh) (many s3)) (next-nat s2))
  (let ((many sr) (many s4)) (next-nat s3))
  (values (MkACN q sl sh sr) s4))

(def-fns _ $ (many rd-cfgs : (subterm many (Nat) k) (many (String) s) -> (many (List (ACN)) xs) (many (List (Pair (Nat) (Nat))) ch) (many (String) r))
  (let-match many k (Succ k1) ((Zero) (values (Nil (ACN)) (Nil (Pair (Nat) (Nat))) s)))
  (let ((many a) (many s1)) (rd-acn s))
  (let ((many cn) (many s2)) (next-nat s1))
  (let ((many o2) (many s3)) (next-nat s2))
  (let ((many rest) (many crest) (many s4)) (notail $ rd-cfgs k1 s3))
  (values (Cons (ACN) a rest) (Cons (Pair (Nat) (Nat)) (MkPair _ _ cn o2) crest) s4))

(def-adts $ (Cert : -> Type)
  enum
  (many MkCert : (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (Nat)) acc) (many (List (ACN)) S)
     (many (List (Pair (Nat) (Nat))) ch) (many (ACN) a0) -> (Cert)))

(def-fns _ $ (many rd-cert : (many (String) s) -> (many (Cert) c) (many (String) r))
  (let ((many ns) (many s1)) (next-nat s))
  (let ((many sy) (many s2)) (rd-bools ns s1))
  (let ((many ne) (many s3)) (next-nat s2))
  (let ((many es) (many s4)) (rd-edges ne s3))
  (let ((many na) (many s5)) (next-nat s4))
  (let ((many acc) (many s6)) (rd-nats na s5))
  (let ((many nc) (many s7)) (next-nat s6))
  (let ((many S) (many ch) (many s8)) (rd-cfgs nc s7))
  (let ((many a0) (many s9)) (rd-acn s8))
  (values (MkCert sy es acc S ch a0) s9))

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

(def-fns _ $ (many eq-edge : (many (Edge) x) (many (Edge) y) -> (many (Maybe (Eq (Edge) x y)) r))
  (let-match many x (MkE a1 b1 c1))
  (let-match many y (MkE a2 b2 c2))
  (let-match many (eq-nat a1 a2) (Some _ e1) ((None _) (None _)))
  (let-match many (eq-nat b1 b2) (Some _ e2) ((None _) (None _)))
  (let-match many (eq-nat c1 c2) (Some _ e3) ((None _) (None _)))
  (let-match many e1 (Refl _ _))
  (let-match many e2 (Refl _ _))
  (let-match many e3 (Refl _ _))
  (Some _ (Refl (Edge) x)))

(def-fns _ $ (many eq-acn : (many (ACN) x) (many (ACN) y) -> (many (Maybe (Eq (ACN) x y)) r))
  (let-match many x (MkACN a1 b1 c1 d1))
  (let-match many y (MkACN a2 b2 c2 d2))
  (let-match many (eq-nat a1 a2) (Some _ e1) ((None _) (None _)))
  (let-match many (eq-nat b1 b2) (Some _ e2) ((None _) (None _)))
  (let-match many (eq-nat c1 c2) (Some _ e3) ((None _) (None _)))
  (let-match many (eq-nat d1 d2) (Some _ e4) ((None _) (None _)))
  (let-match many e1 (Refl _ _))
  (let-match many e2 (Refl _ _))
  (let-match many e3 (Refl _ _))
  (let-match many e4 (Refl _ _))
  (Some _ (Refl (ACN) x)))

(def-fns _ $ (many find-acn : (many (ACN) a) (subterm many (List (ACN)) xs) -> (many (Res (Mem (ACN) a xs)) r))
  (let-match many xs (Cons _ b rest) ((Nil _) (RFail _)))
  (match many (eq-acn a b) _
    ((Some _ e) (let-match many e (Refl _ _)) (ROk _ (MemHere (ACN) a rest)))
    ((None _)
      (let-match many (notail $ find-acn a rest) (ROk _ mm) ((RFail _) (RFail _)))
      (ROk _ (MemThere (ACN) a b rest mm)))))

(def-fns _ $ (many find-edge : (many (Edge) a) (subterm many (List (Edge)) xs) -> (many (Res (Mem (Edge) a xs)) r))
  (let-match many xs (Cons _ b rest) ((Nil _) (RFail _)))
  (match many (eq-edge a b) _
    ((Some _ e) (let-match many e (Refl _ _)) (ROk _ (MemHere (Edge) a rest)))
    ((None _)
      (let-match many (notail $ find-edge a rest) (ROk _ mm) ((RFail _) (RFail _)))
      (ROk _ (MemThere (Edge) a b rest mm)))))

(def-fns _ $ (many find-nat : (many (Nat) a) (subterm many (List (Nat)) xs) -> (many (Res (Mem (Nat) a xs)) r))
  (let-match many xs (Cons _ b rest) ((Nil _) (RFail _)))
  (match many (eq-nat a b) _
    ((Some _ e) (let-match many e (Refl _ _)) (ROk _ (MemHere (Nat) a rest)))
    ((None _)
      (let-match many (notail $ find-nat a rest) (ROk _ mm) ((RFail _) (RFail _)))
      (ROk _ (MemThere (Nat) a b rest mm)))))

(def-fns _ $ (many place-n : (many (Dir) d) (many (Nat) q p c o) -> (many (ACN) a) (erased (PlaceN d q p c o a) pl))
  (match many d _
    ((DL) (values (MkACN q p c o) (PNL q p c o)))
    ((DR) (values (MkACN q o c p) (PNR q p c o)))))

(def-fns _ $ (many all-from : (many (List (ACN)) S) (many (Dir) d) (many (Nat) q o s) (subterm many (List (Edge)) es) ->
    (many (Res (AllFrom S d q o es s)) r))
  (let-match many es (Cons _ e rest) ((Nil _) (ROk _ (AFNil S d q o s))))
  (let-match many e (MkE s1 c s2))
  (let-match many (notail $ all-from S d q o s rest) (ROk _ af) ((RFail _) (RFail _)))
  (match many (nat-eq s1 s) _
    ((Equal _ _ _)
      (let ((many a) (erased pl)) (place-n d q s2 c o))
      (let-match many (find-acn a S) (ROk _ ma) ((RFail _) (RFail _)))
      (ROk _ (AFHit S d q o s c s2 rest a pl ma af)))
    ((Unequal _ _ _ _ ap) (ROk _ (AFSkip S d q o s s1 c s2 rest ap af)))))

(def-fns _ $ (many aokn : (many (List (PT)) p) (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (ACN)) S)
    (many (ACN) a) (many (Nat) cn o2) -> (many (Res (AOKN p sy es S a)) r))
  (let-match many a (MkACN q sl sh sr))
  (let-match many (nth-r _ sy sh) (NOk _ _ _ h nh) ((NNo _ _ _) (RFail _)))
  (let-match many (plook p q h) (PLOk _ _ _ x pl) ((PLNo _ _ _) (RFail _)))
  (let-match many x (Def t) ((Undef) (RFail _)))
  (let-match many t (Go w d q2) ((Halt) (RFail _)))
  (let-match many (nth-r _ sy cn) (NOk _ _ _ w2 nw) ((NNo _ _ _) (RFail _)))
  (let-match many (eq-bit w2 w) (Some _ ew) ((None _) (RFail _)))
  (let-match many ew (Refl _ _))
  (match many d _
    ((DL)
      (let-match many (find-edge (MkE o2 cn sr) es) (ROk _ me) ((RFail _) (RFail _)))
      (let-match many (all-from S (DL) q2 o2 sl es) (ROk _ af) ((RFail _) (RFail _)))
      (ROk _ (AKL p sy es S q sl sh sr q2 cn o2 h w pl nh nw me af)))
    ((DR)
      (let-match many (find-edge (MkE o2 cn sl) es) (ROk _ me) ((RFail _) (RFail _)))
      (let-match many (all-from S (DR) q2 o2 sr es) (ROk _ af) ((RFail _) (RFail _)))
      (ROk _ (AKR p sy es S q sl sh sr q2 cn o2 h w pl nh nw me af)))))

(def-fns _ $ (many closedn : (many (List (PT)) p) (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (ACN)) S)
    (subterm many (List (ACN)) T) (many (List (Pair (Nat) (Nat))) ch) -> (many (Res (ClosedN p sy es S T)) r))
  (let-match many T (Cons _ a rest) ((Nil _) (ROk _ (CNNil p sy es S))))
  (let-match many ch (Cons _ c crest) ((Nil _) (RFail _)))
  (let-match many c (MkPair _ _ cn o2))
  (let-match many (aokn p sy es S a cn o2) (ROk _ ok) ((RFail _) (RFail _)))
  (let-match many (notail $ closedn p sy es S rest crest) (ROk _ cl) ((RFail _) (RFail _)))
  (ROk _ (CNCons p sy es S rest a ok cl)))

(def-adts
  ((BlankR : ((List (Bool)) sy) ((List (Edge)) es) ((List (Nat)) acc) ((Nat) a) -> Type)
    enum
    (many BOk : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (Nat) a) (many (Nat) c a2)
       (erased (Mem (Edge) (MkE a c a2) es) me) (erased (Nth (Bool) sy c (BFalse)) nb) (erased (Mem (Nat) a2 acc) ma) -> (BlankR sy es acc a))
    (many BNo : (erased (List (Bool)) sy) (erased (List (Edge)) es) (erased (List (Nat)) acc) (erased (Nat) a) -> (BlankR sy es acc a))))

(def-fns _ $ (many blank-from : (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (Nat)) acc) (many (Nat) a)
    (subterm many (List (Edge)) es0) -> (many (BlankR sy es acc a) r))
  (let-match many es0 (Cons _ e rest) ((Nil _) (BNo sy es acc a)))
  (let-match many e (MkE s c a2))
  (let ((many next)) (notail $ blank-from sy es acc a rest))
  (let-match many (nat-eq s a) (Equal _ _ _) (else next))
  (let-match many (nth-r _ sy c) (NOk _ _ _ b nb) ((NNo _ _ _) next))
  (let-match many b (BFalse) ((BTrue) next))
  (let-match many (find-nat a2 acc) (ROk _ ma) ((RFail _) next))
  (let-match many (find-edge (MkE a c a2) es) (ROk _ me) ((RFail _) next))
  (BOk sy es acc a c a2 me nb ma))

(def-fns _ $ (many acc-all : (many (List (Bool)) sy) (many (List (Edge)) es) (many (List (Nat)) acc) (subterm many (List (Nat)) as) ->
    (many (Res (AccAll sy es acc as)) r))
  (let-match many as (Cons _ a rest) ((Nil _) (ROk _ (AANil sy es acc))))
  (let-match many (blank-from sy es acc a es) (BOk _ _ _ _ c a2 me nb ma) ((BNo _ _ _ _) (RFail _)))
  (let-match many (notail $ acc-all sy es acc rest) (ROk _ aa) ((RFail _) (RFail _)))
  (ROk _ (AACons sy es acc rest a c a2 me nb ma aa)))

(def-fns _ $ (many check-cert : (many (Nat) k) (many (List (Tr)) O) (many (List (PT)) p) (many (Cert) ct) -> (many (Res (TNode k O p)) r))
  (let-match many ct (MkCert sy es acc S ch a0))
  (let-match many (closedn p sy es S S ch) (ROk _ cl) ((RFail _) (RFail _)))
  (let-match many (acc-all sy es acc acc) (ROk _ aa) ((RFail _) (RFail _)))
  (let-match many (find-acn a0 S) (ROk _ ma) ((RFail _) (RFail _)))
  (let-match many a0 (MkACN q0 sl sh sr))
  (let-match many q0 (Zero) ((Succ _) (RFail _)))
  (let-match many (nth-r _ sy sh) (NOk _ _ _ h nh) ((NNo _ _ _) (RFail _)))
  (let-match many h (BFalse) ((BTrue) (RFail _)))
  (let-match many (find-nat sl acc) (ROk _ ml) ((RFail _) (RFail _)))
  (let-match many (find-nat sr acc) (ROk _ mr) ((RFail _) (RFail _)))
  (ROk _ (TN k O p sy es acc S cl aa a0 ma
    (MkGCN sy es acc (Zero) sl sh sr (Nil (Bool)) (Nil (Bool)) (BFalse) (GAcc sy es acc sl ml) (GAcc sy es acc sr mr) nh))))

(def-fns _
  ((many build : (subterm many (Nat) dep) (subterm many (List (Tr)) os) (many (Nat) k) (many (List (Tr)) O) (many (List (PT)) p) (many (String) hs) ->
       (many (Res (TNode k O p)) r) (many (String) hs2))
    (match many (psim p 30 (Zero) (Zero) (Nil (Bool)) (BFalse) (Nil (Bool)) (PRNil p _)) _
      ((PSHalt _ t q l r h pr pl)
        (let-match many (lt-dec (Succ t) (Succ k)) (Yes _ _ lt) ((No _ _ _) (values (RFail _) hs)))
        (values (ROk _ (TH k O p t q l r h pr pl lt)) hs))
      ((PSUndef _ t q l r h pr pl)
        (let-match many dep (Succ d1) ((Zero) (values (RFail _) hs)))
        (let ((many ra) (many hs1)) (notail $ build-all d1 O k O p q h hs))
        (let-match many ra (ROk _ ta) ((RFail _) (values (RFail _) hs1)))
        (values (ROk _ (TS k O p t q l r h pr pl ta)) hs1))
      ((PSOut _)
        (let ((many ct) (many hs1)) (rd-cert hs))
        (values (check-cert k O p ct) hs1))))
  ((many build-all : (subterm many (Nat) dep) (subterm many (List (Tr)) os) (many (Nat) k) (many (List (Tr)) O) (many (List (PT)) p)
       (many (Nat) q) (many (Bool) h) (many (String) hs) -> (many (Res (TAll k O p q h os)) r) (many (String) hs2))
    (let-match many os (Cons _ x rest) ((Nil _) (values (ROk _ (TANil k O p q h)) hs)))
    (let-match many (pset p q h (Def x)) (PSOk _ _ _ _ p2 ps) ((PSNo _ _ _ _) (values (RFail _) hs)))
    (let ((many rn) (many hs1)) (notail $ build dep rest k O p2 hs))
    (let-match many rn (ROk _ tn) ((RFail _) (values (RFail _) hs1)))
    (let ((many ra) (many hs2)) (notail $ build-all dep rest k O p q h hs1))
    (let-match many ra (ROk _ ta) ((RFail _) (values (RFail _) hs2)))
    (values (ROk _ (TACons k O p p2 q h x rest ps tn ta)) hs2)))

(def-adts
  ((UList : ((Nat) k) ((List (PT)) p) -> Type)
    enum
    (many UNil : -> (UList (Zero) (Nil (PT))))
    (many UCons : (erased (Nat) k) (erased (List (PT)) p) (erased (UList k p) u) -> (UList (Succ k) (Cons (PT) (Undef) (Cons (PT) (Undef) p))))))

(def-fns _ $ (many undefs : (subterm many (Nat) k) -> (many (List (PT)) p) (erased (UList k p) u))
  (let-match many k (Succ k1) ((Zero) (values (Nil (PT)) (UNil))))
  (let ((many p) (erased u)) (notail $ undefs k1))
  (values (Cons (PT) (Undef) (Cons (PT) (Undef) p)) (UCons k1 p u)))

(def-fns _ $ (erased ext-undef : (erased (Nat) n k) (erased (List (Tr)) m) (erased (List (PT)) p)
    (subterm erased (Rows n k m) rw) (erased (UList k p) u) -> (erased (Ext p m) e))
  (match erased rw _
    ((RowsZ _) (let-match erased u (UNil)) (ExNil))
    ((RowsS _ k1 t0 t1 rest _ _ rw1)
      (let-match erased u (UCons _ p1 u1))
      (ExU t0 (Cons (PT) (Undef) p1) (Cons (Tr) t1 rest) (ExU t1 p1 rest (ext-undef n k1 rest p1 rw1 u1))))))

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
