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

(def-lvl COB)

; Levels for the co-closure of a set closed at L, given to a function at Y: the rotation of the set at R and the walk at W.
(def-adts $ (CoLv : ((Level) L Y) -> Type)
  enum
  (many MkCoLv : (erased (Level) L R W Y) (erased (Predates (Level) COB R) pb) (erased (Predates (Level) L R) p1) (erased (Predates (Level) R W) p2)
      (erased (Predates (Level) W Y) p3) -> (CoLv L Y)))

; The rotation P o rotr 1 of a Kempe-closed P is Kempe-closed (closedP1 in check_reducible_valid), at a level M above P's and COB.
(def-fns _ $ (erased kclosed-rot : (erased (Level) L M) (erased (Predates (Level) L M) pl) (erased (Predates (Level) COB M) pb) ->
    (erased (Fn M (erased Pred P2) (erased Rel R) (erased (KClosed L P2 R) cl) -> (erased (KClosed M (MkPred (PredC) P2 RotP) (MkRel (RelC) R RotR)) c2)) f))
  (let ((erased q1) (erased q2) (erased q3) (erased q4) (erased q5) (erased q6))
    (values (predates-trans (prove-predates (level-of permt-snoc) COB) pb) (predates-trans (prove-predates (level-of mg-bal) COB) pb)
      (predates-trans (prove-predates (level-of grot-exists) COB) pb) (predates-trans (prove-predates (level-of rot-fwd) COB) pb)
      (predates-trans (prove-predates (level-of rot-unsnoc) COB) pb) (predates-trans (prove-predates (level-of rot-bwd) COB) pb)))
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
        (let ((erased et2) (erased e2) (erased s2) (erased pt2) (erased pc)) (permt-snoc (predates q1) g et ct ct2 e pt s))
        (MkHolds (PredC) P2 RotP ct2 (MkRotP P2 et2 ct2 e2 s2 (cpf (predates pl) (Cons _ e et) (Cons _ e2 et2) g ip (PTCons g e e2 et et2 pc pt2) hp)))))
    (def-fns M
      ((erased cg1 : (erased (List (Col)) ct) (erased (Holds P1 ct) p) -> (erased (List (Gsym)) w1) (erased (MatchG (BS0) ct w1) m) (erased (HoldsR R1 ct w1) r))
        (let-match erased p (MkHolds _ _ _ _ h))
        (let-match erased h (MkRotP _ et _ e s hp))
        (let ((erased w) (erased mw) (erased rr)) (cgf (predates pl) (Cons _ e et) hp))
        (let ((erased b) (erased bl)) (mg-bal (predates q2) (Cons _ e et) w mw))
        (let ((erased w1) (erased g)) (grot-exists (predates q3) b w bl))
        (let ((erased m1)) (rot-fwd (predates q4) b w w1 e et ct g mw s))
        (values w1 m1 (MkHoldsR (RelC) R RotR ct w1 (MkRotR R et ct e w w1 s rr mw g)))))
    (def-fns M
      ((erased cm1 : (erased (List (Col)) ct ct2) (erased (List (Gsym)) w1) (erased (HoldsR R1 ct w1) r) (erased (MatchG (BS0) ct2 w1) m) ->
          (erased (Holds P1 ct2) q))
        (let-match erased r (MkHoldsR _ _ _ _ _ h))
        (let-match erased h (MkRotR _ et _ e w _ s rr mw g))
        (let ((erased et2) (erased e2) (erased s2)) (rot-unsnoc (predates q5) w w1 e et ct2 g mw m))
        (let ((erased b) (erased bl)) (mg-bal (predates q2) (Cons _ e et) w mw))
        (let ((erased mw2)) (rot-bwd (predates q6) b w w1 e2 et2 ct2 bl g m s2))
        (MkHolds (PredC) P2 RotP ct2 (MkRotP P2 et2 ct2 e2 s2 (cmf (predates pl) (Cons _ e et) (Cons _ e2 et2) w rr mw2)))))
    (MkKClosed M P1 R1 cp1 cg1 cm1))
  rot-closed)

; After Kempe_coclosure of chromogram.v, for the Kempe-closed sets whose closure functions are at level L, by a function at
; level Y: every such set holding et holds a trace of P.
(def-adts $ (KCoclo : ((Level) L Y) ((PredC) P) ((List (Col)) et) -> Type)
  enum
  (many MkKCoclo : (erased (Level) L Y) (erased (PredC) P) (erased (List (Col)) et)
      (erased (Fn Y (erased Pred P2) (erased Rel R) (erased (KClosed L P2 R) cl) (erased (Holds P2 et) p) ->
          (erased (List (Col)) et2) (erased (Holds P et2) q) (erased (Holds P2 et2) p2)) f)
      -> (KCoclo L Y P et)))

; From the co-closure of the rotated ring traces at the rotation ct of e0 :: et, the co-closure of the ring traces at e0 :: et.
(def-fns _ $ (erased kcc-ring : (erased (List (Step)) cp) (erased (List (Col)) et ct) (erased (Col) e0) (erased (KCC (MkPred (List (Step)) cp CpColR) ct) k)
    (erased (Snoc (Col) et e0 ct) s) (erased (Level) L Y) (erased (CoLv L Y) lv) -> (erased (KCoclo L Y (MkPred (List (Step)) cp CpCol) (Cons (Col) e0 et)) r))
  (let-match erased lv (MkCoLv _ M1 M2 _ pb p1 p2 p3))
  (let ((erased rot)) (kclosed-rot L M1 p1 pb))
  (let ((erased walk)) (kcc-coclosure M1 M2 p2 (predates-trans (predates-trans (prove-predates KCB COB) pb) p2)))
  (let ((erased q1)) (predates-trans p2 p3))
  (let ((erased q2)) (predates-trans (prove-predates (level-of snoc-inj) COB) (predates-trans pb q1)))
  (def-fns Y $ (erased g : (erased Pred P2) (erased Rel R) (erased (KClosed L P2 R) cl) (erased (Holds P2 (Cons (Col) e0 et)) p) ->
      (erased (List (Col)) et2) (erased (Holds (MkPred (List (Step)) cp CpCol) et2) q) (erased (Holds P2 et2) p2))
    (let ((erased ct2) (erased q) (erased p2))
      (walk (predates p3) (MkPred (List (Step)) cp CpColR) (MkPred (PredC) P2 RotP) (MkRel (RelC) R RotR) (rot (predates q1) P2 R cl) ct k (MkHolds (PredC) P2 RotP ct (MkRotP P2 et ct e0 s p))))
    (let-match erased q (MkHolds _ _ _ _ hq))
    (let-match erased hq (MkCpColR _ et1 _ e1 s1 c))
    (let-match erased p2 (MkHolds _ _ _ _ hp))
    (let-match erased hp (MkRotP _ et3 _ e3 s3 hp3))
    (let-match erased (snoc-inj (predates q2) (Col) et1 et3 ct2 e1 e3 s1 s3) (Refl _ _))
    (values (Cons _ e1 et1) (MkHolds (List (Step)) cp CpCol (Cons _ e1 et1) c) hp3))
  (MkKCoclo L Y (MkPred (List (Step)) cp CpCol) (Cons _ e0 et) g))

(def-lvl KHL)

; The Kempe half of check_reducible_valid, by a function at level KHL: every trace e0 :: et of cprsize cp entries whose even
; normal form of et is not in the Kempe tree kt is in the co-closure of the ring traces of cp's map, for the closed sets at any
; level L with levels CoLv L Y.

(def-adts $ (KHalf : ((List (Step)) cp) ((Ctree) kt) -> Type)
  enum
  (many MkKHalf : (erased (List (Step)) cp) (erased (Ctree) kt)
      (erased (Fn KHL (erased (List (Col)) cs et et2) (erased (Col) e0) (erased (Nat) k) (erased (Trace cs (Cons (Col) e0 et)) tr)
          (erased (Length (Col) (Cons (Col) e0 et) k) l) (erased (Cprsize cp k) c) (erased (ETrace et et2) e) (erased (CtSub kt et2 (Zero)) m)
          (erased (Level) L Y) (erased (CoLv L Y) lv) -> (erased (KCoclo L Y (MkPred (List (Step)) cp CpCol) (Cons (Col) e0 et)) r)) f)
      -> (KHalf cp kt)))

(def-fns _ $ (erased kempe-half : (erased (List (Step)) cp) (erased (Nat) h) (erased (Ctree) kt) (erased (KSound (MkPred (List (Step)) cp CpColR) h kt) ks)
    (erased (Cprsize cp (Succ (Succ h))) cs0) -> (erased (KHalf cp kt) r))
  (def-fns KHL $ (erased f : (erased (List (Col)) cs et et2) (erased (Col) e0) (erased (Nat) k) (erased (Trace cs (Cons (Col) e0 et)) tr)
      (erased (Length (Col) (Cons (Col) e0 et) k) l) (erased (Cprsize cp k) c) (erased (ETrace et et2) e) (erased (CtSub kt et2 (Zero)) m)
      (erased (Level) L Y) (erased (CoLv L Y) lv) -> (erased (KCoclo L Y (MkPred (List (Step)) cp CpCol) (Cons (Col) e0 et)) r))
    (let-match erased (cprsize-fn cp k (Succ (Succ h)) c cs0) (Refl _ _))
    (let-match erased l (LengthCons _ _ _ _ l1))
    (let ((erased ct2) (erased cr) (erased s)) (trace-ctr cs et e0 tr))
    (kcc-ring cp et ct2 e0 (kempe-treeP-c (MkPred (List (Step)) cp CpColR) h kt ks et et2 ct2 l1 e m cr) s L Y lv))
  (MkKHalf cp kt f))

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

; The map of cp is C-reducible with contract cc (C_reducible of coloring.v, for the ring of cfring of cfmap.v), by a function
; at level X, for the Kempe-closed sets at every level L with levels CoLv L Y.
(def-adts $ (CRed : ((Level) X) ((List (Step)) cp) ((List (Nat)) cc) -> Type)
  enum
  (many MkCRed : (erased (Level) X) (erased (List (Step)) cp) (erased (List (Nat)) cc) (erased (Nat) d) (erased (List (Nat)) e n f r) (erased (Cpmap cp d e f r) c)
      (erased (Hypermap d e n f) h) (erased (ValidContract e n f r cc) v)
      (erased (Fn X (erased (List (Col)) et) (erased (CcCol cp cc et) col) (erased (Level) L Y) (erased (CoLv L Y) lv)
          -> (erased (KCoclo L Y (MkPred (List (Step)) cp CpCol) et) k)) g)
      -> (CRed X cp cc)))

; The contract half of check_reducible_valid for the Kempe tree kt: cc is valid, and the even normal form of every contract ring
; trace without its first entry is not in kt, by a function at level G.
(def-adts $ (ContractOK : ((Level) G) ((List (Step)) cp) ((List (Nat)) cc) ((Ctree) kt) -> Type)
  enum
  (many MkContractOK : (erased (Level) G) (erased (List (Step)) cp) (erased (List (Nat)) cc) (erased (Ctree) kt) (erased (Nat) d) (erased (List (Nat)) e n f r)
      (erased (Cpmap cp d e f r) c) (erased (Hypermap d e n f) h) (erased (ValidContract e n f r cc) v)
      (erased (Fn G (erased (List (Col)) et) (erased (CcCol cp cc et) col) -> (erased (Col) e0) (erased (List (Col)) et1 et2)
          (erased (Eq (List (Col)) et (Cons (Col) e0 et1)) q) (erased (ETrace et1 et2) tr) (erased (CtSub kt et2 (Zero)) m)) g)
      -> (ContractOK G cp cc kt)))

; check_reducible_valid, with the contract half stated against the Kempe tree, for a level X above KHL and G.
(def-fns _ $ (erased check-reducible-valid : (erased (Level) X G) (erased (Predates (Level) KHL X) pk) (erased (Predates (Level) G X) pg)
    (erased (List (Step)) cp) (erased (List (Nat)) cc) (erased (Ctree) kt) (erased (KHalf cp kt) kh) (erased (ContractOK G cp cc kt) ok) -> (erased (CRed X cp cc) r))
  (let-match erased kh (MkKHalf _ _ kf))
  (let-match erased ok (MkContractOK _ _ _ _ d e n f r c h v cg))
  (let ((erased q1) (erased q2) (erased q3) (erased q4))
    (values (predates-trans (prove-predates (level-of cpmap-size) KHL) pk) (predates-trans (prove-predates (level-of trace-length) KHL) pk)
      (predates-trans (prove-predates (level-of ncols-length) KHL) pk) (predates-trans (prove-predates (level-of respects-length) KHL) pk)))
  (def-fns X $ (erased g : (erased (List (Col)) et) (erased (CcCol cp cc et) col) (erased (Level) L Y) (erased (CoLv L Y) lv)
      -> (erased (KCoclo L Y (MkPred (List (Step)) cp CpCol) et) k))
    (let ((erased e0) (erased et1) (erased et2) (erased q) (erased tr) (erased m)) (cg (predates pg) et col))
    (let-match erased q (Refl _ _))
    (let-match erased col (MkCcCol _ _ d2 e2 f2 r2 ks rc cs _ c2 _ rr nc trc))
    (let ((erased k) (erased lk) (erased csz)) (cpmap-size (predates q1) cp d2 e2 f2 r2 c2))
    (kf (predates pk) cs et1 et2 e0 k trc (trace-length (predates q2) cs et k trc (ncols-length (predates q3) rc cs k nc (respects-length (predates q4) ks r2 rc k rr lk)))
      csz tr m L Y lv))
  (MkCRed X cp cc d e n f r c h v g))
