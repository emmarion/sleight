; The Kempe half of check_reducible_valid of cfreducible.v. Load after check.sl and gramrot.sl.

; P holds of ct with its last entry moved to the front (P o rotr 1).
(def-adts $ (RotP : ((PredC) p) ((List (Col)) ct) -> Type)
  enum
  (many MkRotP : (erased (PredC) p) (erased (List (Col)) et ct) (erased (Col) e) (erased (Snoc (Col) et e ct) s) (erased (Holds p (Cons (Col) e et)) h)
      -> (RotP p ct)))

; w1 rotates a chromogram w that r relates to ct with its last entry moved to the front.
(def-adts $ (RotR : ((RelC) r) ((List (Col)) ct) ((List (Gsym)) w1) -> Type)
  enum
  (many MkRotR : (erased (RelC) r) (erased (List (Col)) et ct) (erased (Col) e) (erased (List (Gsym)) w w1) (erased (Snoc (Col) et e ct) s)
      (erased (HoldsR r (Cons (Col) e et) w) h) (erased (MatchG (BS0) (Cons (Col) e et) w) m) (erased (GRot w w1) g) -> (RotR r ct w1)))

(def-fns _ $ (erased permt-snoc : (erased (Perm) g) (erased (List (Col)) et ct ct2) (erased (Col) e) (erased (PermT g ct ct2) pt) (subterm erased (Snoc (Col) et e ct) s)
    -> (erased (List (Col)) et2) (erased (Col) e2) (erased (Snoc (Col) et2 e2 ct2) s2) (erased (PermT g et et2) pt2) (erased (PermC g e e2) pc))
  (match erased s _
    ((SnocNil _ _) (let-match erased pt (PTCons _ _ e2 _ et3 pc pt1)) (let-match erased pt1 (PTNil _)) (values (Nil _) e2 (SnocNil _ e2) (PTNil g) pc))
    ((SnocCons _ x _ et1 ct1 s1)
      (let-match erased pt (PTCons _ _ x2 _ ct3 px pt1))
      (let ((erased et2) (erased e2) (erased s2) (erased pt2) (erased pc)) (permt-snoc g et1 ct1 ct3 e pt1 s1))
      (values (Cons _ x2 et2) e2 (SnocCons _ x2 e2 et2 ct3 s2) (PTCons g x x2 et1 et2 px pt2) pc))))

(def-fns _ $ (erased snoc-inj : (erased Type A) (erased (List A) xs ys zs) (erased A x y) (subterm erased (Snoc A xs x zs) p) (erased (Snoc A ys y zs) q)
    -> (erased (Eq (List A) (Cons A x xs) (Cons A y ys)) e))
  (match erased p _
    ((SnocNil _ _) (match erased q _ ((SnocNil _ _) (Refl _ (Cons A x xs))) (absurd (SnocCons _ _ _ _ _ q1) q1)))
    ((SnocCons _ a _ xs1 zs1 p1)
      (match erased q _
        (absurd (SnocNil _ _) p1)
        ((SnocCons _ _ _ ys1 _ q1) (let-match erased (snoc-inj A xs1 ys1 zs1 x y p1 q1) (Refl _ _)) (Refl _ (Cons A x xs)))))))

; The rotation P o rotr 1 of a Kempe-closed P is Kempe-closed (closedP1 in check_reducible_valid), at a level above P's.
(def-fns _ $ (erased kclosed-rot : (erased (Level) L) -> (erased (Level) M)
    (erased (Fn M (erased Pred P2) (erased Rel R) (erased (KClosed L P2 R) cl) -> (erased (KClosed M (MkPred (PredC) P2 RotP) (MkRel (RelC) R RotR)) c2)) f))
  (def-lvl M)
  (def-fns M $ (erased rot-closed : (erased Pred P2) (erased Rel R) (erased (KClosed L P2 R) cl) ->
      (erased (KClosed M (MkPred (PredC) P2 RotP) (MkRel (RelC) R RotR)) c2))
    (let-match erased cl (MkKClosed _ _ _ cpf cgf cmf))
    (let ((erased P1)) (MkPred (PredC) P2 RotP))
    (let ((erased R1)) (MkRel (RelC) R RotR))
    (def-fns M
      ((erased cp1 : (erased (List (Col)) ct ct2) (erased (Perm) g) (erased (IsPerm g) ip) (erased (PermT g ct ct2) pt) (erased (Holds P1 ct) p) ->
          (erased (Holds P1 ct2) q))
        (let-match erased p (MkHolds _ _ _ _ h))
        (let-match erased h (MkRotP _ et _ e s hp))
        (let ((erased et2) (erased e2) (erased s2) (erased pt2) (erased pc)) (permt-snoc g et ct ct2 e pt s))
        (MkHolds (PredC) P2 RotP ct2 (MkRotP P2 et2 ct2 e2 s2 (cpf (Cons _ e et) (Cons _ e2 et2) g ip (PTCons g e e2 et et2 pc pt2) hp)))))
    (def-fns M
      ((erased cg1 : (erased (List (Col)) ct) (erased (Holds P1 ct) p) -> (erased (List (Gsym)) w1) (erased (MatchG (BS0) ct w1) m) (erased (HoldsR R1 ct w1) r))
        (let-match erased p (MkHolds _ _ _ _ h))
        (let-match erased h (MkRotP _ et _ e s hp))
        (let ((erased w) (erased mw) (erased rr)) (cgf (Cons _ e et) hp))
        (let ((erased b) (erased bl)) (mg-bal (Cons _ e et) w mw))
        (let ((erased w1) (erased g)) (grot-exists b w bl))
        (let ((erased m1)) (rot-fwd b w w1 e et ct g mw s))
        (values w1 m1 (MkHoldsR (RelC) R RotR ct w1 (MkRotR R et ct e w w1 s rr mw g)))))
    (def-fns M
      ((erased cm1 : (erased (List (Col)) ct ct2) (erased (List (Gsym)) w1) (erased (HoldsR R1 ct w1) r) (erased (MatchG (BS0) ct2 w1) m) ->
          (erased (Holds P1 ct2) q))
        (let-match erased r (MkHoldsR _ _ _ _ _ h))
        (let-match erased h (MkRotR _ et _ e w _ s rr mw g))
        (let ((erased et2) (erased e2) (erased s2)) (rot-unsnoc w w1 e et ct2 g mw m))
        (let ((erased b) (erased bl)) (mg-bal (Cons _ e et) w mw))
        (let ((erased mw2)) (rot-bwd b w w1 e2 et2 ct2 bl g m s2))
        (MkHolds (PredC) P2 RotP ct2 (MkRotP P2 et2 ct2 e2 s2 (cmf (Cons _ e et) (Cons _ e2 et2) w rr mw2)))))
    (MkKClosed M P1 R1 cp1 cg1 cm1))
  (values M rot-closed))

; After Kempe_coclosure of chromogram.v, for the Kempe-closed sets whose closure functions are at level L: every such set
; holding et holds a trace of P.
(def-adts $ (KCoclo : ((Level) L) ((PredC) P) ((List (Col)) et) -> Type)
  enum
  (many MkKCoclo : (erased (Level) L M) (erased (PredC) P) (erased (List (Col)) et)
      (erased (Fn M (erased Pred P2) (erased Rel R) (erased (KClosed L P2 R) cl) (erased (Holds P2 et) p) ->
          (erased (List (Col)) et2) (erased (Holds P et2) q) (erased (Holds P2 et2) p2)) f)
      -> (KCoclo L P et)))

; From the co-closure of the rotated ring traces at the rotation ct of e0 :: et, the co-closure of the ring traces at e0 :: et.
(def-fns _ $ (erased kcc-ring : (erased (List (Step)) cp) (erased (List (Col)) et ct) (erased (Col) e0) (erased (KCC (MkPred (List (Step)) cp CpColR) ct) k)
    (erased (Snoc (Col) et e0 ct) s) (erased (Level) L) -> (erased (KCoclo L (MkPred (List (Step)) cp CpCol) (Cons (Col) e0 et)) r))
  (let ((erased M1) (erased rot)) (kclosed-rot L))
  (let ((erased M2) (erased walk)) (kcc-coclosure M1))
  (def-lvl M3)
  (def-fns M3 $ (erased g : (erased Pred P2) (erased Rel R) (erased (KClosed L P2 R) cl) (erased (Holds P2 (Cons (Col) e0 et)) p) ->
      (erased (List (Col)) et2) (erased (Holds (MkPred (List (Step)) cp CpCol) et2) q) (erased (Holds P2 et2) p2))
    (let ((erased ct2) (erased q) (erased p2))
      (walk (MkPred (List (Step)) cp CpColR) (MkPred (PredC) P2 RotP) (MkRel (RelC) R RotR) (rot P2 R cl) ct k (MkHolds (PredC) P2 RotP ct (MkRotP P2 et ct e0 s p))))
    (let-match erased q (MkHolds _ _ _ _ hq))
    (let-match erased hq (MkCpColR _ et1 _ e1 s1 c))
    (let-match erased p2 (MkHolds _ _ _ _ hp))
    (let-match erased hp (MkRotP _ et3 _ e3 s3 hp3))
    (let-match erased (snoc-inj (Col) et1 et3 ct2 e1 e3 s1 s3) (Refl _ _))
    (values (Cons _ e1 et1) (MkHolds (List (Step)) cp CpCol (Cons _ e1 et1) c) hp3))
  (MkKCoclo L M3 (MkPred (List (Step)) cp CpCol) (Cons _ e0 et) g))

(def-fns _ $ (erased disj-sub : (erased (Ctree) tl tr) (erased (List (Col)) et) (erased (CtDisj tl tr) d) (erased (CtMem tr et) m) -> (erased (CtSub tl et (Zero)) s))
  (let ((erased n) (erased s)) (sub-exists tl et))
  (match erased n _ ((Zero) s) (absurd (Succ n1) (disj-mem tl tr et d (MkCtMem tl et n1 s) m))))

; The Kempe half of check_reducible_valid: every trace e0 :: et of cprsize cp entries whose even normal form of et is in ct is in
; the co-closure of the ring traces of cp's map, for the closed sets at any level.
(def-adts $ (KHalf : ((List (Step)) cp) ((Ctree) ct) -> Type)
  enum
  (many MkKHalf : (erased (List (Step)) cp) (erased (Ctree) ct) (erased (Level) F)
      (erased (Fn F (erased (List (Col)) cs et et2) (erased (Col) e0) (erased (Nat) k) (erased (Trace cs (Cons (Col) e0 et)) tr)
          (erased (Length (Col) (Cons (Col) e0 et) k) l) (erased (Cprsize cp k) c) (erased (ETrace et et2) e) (erased (CtMem ct et2) m) (erased (Level) L)
          -> (erased (KCoclo L (MkPred (List (Step)) cp CpCol) (Cons (Col) e0 et)) r)) f)
      -> (KHalf cp ct)))

(def-fns _ $ (erased kempe-half : (erased (List (Step)) cp) (erased (Nat) h) (erased (Ctree) kt ct) (erased (KSound (MkPred (List (Step)) cp CpColR) h kt) ks)
    (erased (Cprsize cp (Succ (Succ h))) cs0) (erased (CtDisj kt ct) dj) -> (erased (KHalf cp ct) r))
  (def-lvl F)
  (def-fns F $ (erased f : (erased (List (Col)) cs et et2) (erased (Col) e0) (erased (Nat) k) (erased (Trace cs (Cons (Col) e0 et)) tr)
      (erased (Length (Col) (Cons (Col) e0 et) k) l) (erased (Cprsize cp k) c) (erased (ETrace et et2) e) (erased (CtMem ct et2) m) (erased (Level) L)
      -> (erased (KCoclo L (MkPred (List (Step)) cp CpCol) (Cons (Col) e0 et)) r))
    (let-match erased (cprsize-fn cp k (Succ (Succ h)) c cs0) (Refl _ _))
    (let-match erased l (LengthCons _ _ _ _ l1))
    (let ((erased ct2) (erased cr) (erased s)) (trace-ctr cs et e0 tr))
    (kcc-ring cp et ct2 e0 (kempe-treeP-c (MkPred (List (Step)) cp CpColR) h kt ks et et2 ct2 l1 e (disj-sub kt ct et2 dj m) cr) s L))
  (MkKHalf cp ct F f))

; C-reducibility of coloring.v, on the maps of cpmap.sl.

; ie lists each dart of cc followed by its edge image (Gonthier's insertE).
(def-adts $ (InsertE : ((List (Nat)) e cc ie) -> Type)
  enum
  (many IENil : (erased (List (Nat)) e) -> (InsertE e (Nil (Nat)) (Nil (Nat))))
  (many IECons : (erased (List (Nat)) e cc ie) (erased (Nat) y z) (erased (Nth (Nat) e y z) p) (erased (InsertE e cc ie) rest)
      -> (InsertE e (Cons (Nat) y cc) (Cons (Nat) y (Cons (Nat) z ie)))))

; From dart x on, the colours ke of the edge images equal the colours ks exactly at the darts of ie.
(def-adts $ (CcEdge : ((List (Nat)) ie) ((Nat) x) ((List (Nat)) ke ks) -> Type)
  enum
  (many CENil : (erased (List (Nat)) ie) (erased (Nat) x) -> (CcEdge ie x (Nil (Nat)) (Nil (Nat))))
  (many CEIn : (erased (List (Nat)) ie ke ks) (erased (Nat) x a) (erased (In x ie) p) (erased (CcEdge ie (Succ x) ke ks) rest)
      -> (CcEdge ie x (Cons (Nat) a ke) (Cons (Nat) a ks)))
  (many CEOut : (erased (List (Nat)) ie ke ks) (erased (Nat) x a b) (erased (NotIn x ie) p) (erased (Apart (Nat) Lt a b) ne) (erased (CcEdge ie (Succ x) ke ks) rest)
      -> (CcEdge ie x (Cons (Nat) a ke) (Cons (Nat) b ks))))

; ks is a colouring of the map (e, f) for the contract cc (Gonthier's cc_coloring), with colours below 4.
(def-adts $ (CcColoring : ((List (Nat)) e f cc ks) -> Type)
  enum
  (many MkCcColoring : (erased (List (Nat)) e f cc ks ie ke) (erased (InsertE e cc ie) pi) (erased (Respects ks f ks) face) (erased (Respects ks e ke) ce)
      (erased (CcEdge ie (Zero) ke ks) edge) (erased (Under ks 4) four) -> (CcColoring e f cc ks)))

; et is the ring trace of a colouring of the map of cp for the contract cc (cc_ring_trace of coloring.v, on the ring of CpCol).
(def-adts $ (CcCol : ((List (Step)) cp) ((List (Nat)) cc) ((List (Col)) et) -> Type)
  enum
  (many MkCcCol : (erased (List (Step)) cp) (erased (List (Nat)) cc) (erased (Nat) d) (erased (List (Nat)) e f r ks rc) (erased (List (Col)) cs et)
      (erased (Cpmap cp d e f r) c) (erased (CcColoring e f cc ks) col) (erased (Respects ks r rc) rr) (erased (NCols rc cs) nc) (erased (Trace cs et) tr)
      -> (CcCol cp cc et)))

; os is the face orbit of x, starting at x.
(def-adts $ (Orbit : ((List (Nat)) p) ((Nat) x) ((List (Nat)) os) -> Type)
  enum
  (many MkOrbit : (erased (List (Nat)) p xs) (erased (Nat) x y) (erased (Nth (Nat) p x y) px) (erased (Path p (Cons (Nat) x (Nil (Nat))) y x xs) w)
      -> (Orbit p x (Cons (Nat) x xs))))

; No edge image of a dart of os is on the face of y: a labelling constant along f tells them apart.
(def-adts $ (NotAdj : ((List (Nat)) e f os) ((Nat) y) -> Type)
  enum
  (many MkNotAdj : (erased (List (Nat)) e f os lab eos ls) (erased (Nat) y l) (erased (Respects lab f lab) rf) (erased (Respects e os eos) re)
      (erased (Respects lab eos ls) rl) (erased (Nth (Nat) lab y l) py) (erased (NotIn l ls) out) -> (NotAdj e f os y)))

; The edge image of y is on the face of a dart of p.
(def-adts $ (EBand : ((List (Nat)) e f p) ((Nat) y) -> Type)
  enum
  (many MkEBand : (erased (List (Nat)) e f p) (erased (Nat) y z) (erased (Nth (Nat) e y z) pz) (erased (Fband f p z) b) -> (EBand e f p y)))

; x is a triad for p (Gonthier's triad): three darts of its face have their edge images on faces of p, and some dart of p
; is not adjacent to x.
(def-adts $ (Triad : ((List (Nat)) e f p) ((Nat) x) -> Type)
  enum
  (many MkTriad : (erased (List (Nat)) e f p os) (erased (Nat) x y1 y2 y3 y) (erased (Orbit f x os) o) (erased (In y1 os) i1) (erased (In y2 os) i2)
      (erased (In y3 os) i3) (erased (Distinct (Cons (Nat) y1 (Cons (Nat) y2 (Cons (Nat) y3 (Nil (Nat)))))) dy) (erased (EBand e f p y1) b1)
      (erased (EBand e f p y2) b2) (erased (EBand e f p y3) b3) (erased (In y p) iy) (erased (NotAdj e f os y) na) -> (Triad e f p x)))

; cc has one to four darts, and a triad in the kernel of r if four.
(def-adts $ (CcSize : ((List (Nat)) e f r ie cc) -> Type)
  enum
  (many CsSmall : (erased (List (Nat)) e f r ie cc) (erased (Nat) k) (erased (Length (Nat) cc k) l) (erased (Lt (Zero) k) lo) (erased (Lt k 4) hi)
      -> (CcSize e f r ie cc))
  (many CsTriad : (erased (List (Nat)) e f r ie cc) (erased (Nat) x) (erased (Length (Nat) cc 4) l) (erased (Kernel f r x) kx) (erased (Triad e f ie x) t)
      -> (CcSize e f r ie cc)))

; cc is a valid contract for the ring r (Gonthier's valid_contract).
(def-adts $ (ValidContract : ((List (Nat)) e n f r cc) -> Type)
  enum
  (many MkValidContract : (erased (List (Nat)) e n f r cc ie) (erased (InsertE e cc ie) pi) (erased (Disj r ie) off) (erased (Simple n ie) sp)
      (erased (CcSize e f r ie cc) sz) -> (ValidContract e n f r cc)))

; The map of cp is C-reducible with contract cc (C_reducible of coloring.v, for the ring of cfring of cfmap.v), for the
; Kempe-closed sets at every level.
(def-adts $ (CRed : ((List (Step)) cp) ((List (Nat)) cc) -> Type)
  enum
  (many MkCRed : (erased (List (Step)) cp) (erased (List (Nat)) cc) (erased (Nat) d) (erased (List (Nat)) e n f r) (erased (Cpmap cp d e f r) c)
      (erased (Hypermap d e n f) h) (erased (ValidContract e n f r cc) v) (erased (Level) F)
      (erased (Fn F (erased (List (Col)) et) (erased (CcCol cp cc et) col) (erased (Level) L) -> (erased (KCoclo L (MkPred (List (Step)) cp CpCol) et) k)) g)
      -> (CRed cp cc)))

; What contract_ctreeP of cfcontract.v gives for a contract tree ct: cc is valid, and the even normal form of every contract
; ring trace without its first entry is in ct.
(def-adts $ (ContractOK : ((List (Step)) cp) ((List (Nat)) cc) ((Ctree) ct) -> Type)
  enum
  (many MkContractOK : (erased (List (Step)) cp) (erased (List (Nat)) cc) (erased (Ctree) ct) (erased (Nat) d) (erased (List (Nat)) e n f r)
      (erased (Cpmap cp d e f r) c) (erased (Hypermap d e n f) h) (erased (ValidContract e n f r cc) v) (erased (Level) G)
      (erased (Fn G (erased (List (Col)) et) (erased (CcCol cp cc et) col) -> (erased (Col) e0) (erased (List (Col)) et1 et2)
          (erased (Eq (List (Col)) et (Cons (Col) e0 et1)) q) (erased (ETrace et1 et2) tr) (erased (CtMem ct et2) m)) g)
      -> (ContractOK cp cc ct)))

; check_reducible_valid, given contract_ctreeP for the contract tree.
(def-fns _ $ (erased check-reducible-valid : (erased (List (Step)) cp) (erased (List (Nat)) cc) (erased (Ctree) ct) (erased (KHalf cp ct) kh)
    (erased (ContractOK cp cc ct) ok) -> (erased (CRed cp cc) r))
  (let-match erased kh (MkKHalf _ _ F0 kf))
  (let-match erased ok (MkContractOK _ _ _ d e n f r c h v G cg))
  (def-lvl F)
  (def-fns F $ (erased g : (erased (List (Col)) et) (erased (CcCol cp cc et) col) (erased (Level) L) -> (erased (KCoclo L (MkPred (List (Step)) cp CpCol) et) k))
    (let ((erased e0) (erased et1) (erased et2) (erased q) (erased tr) (erased m)) (cg et col))
    (let-match erased q (Refl _ _))
    (let-match erased col (MkCcCol _ _ d2 e2 f2 r2 ks rc cs _ c2 _ rr nc trc))
    (let ((erased k) (erased lk) (erased csz)) (cpmap-size cp d2 e2 f2 r2 c2))
    (kf cs et1 et2 e0 k trc (trace-length cs et k trc (ncols-length rc cs k nc (respects-length ks r2 rc k rr lk))) csz tr m L))
  (MkCRed cp cc d e n f r c h v F g))
