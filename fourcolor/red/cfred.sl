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
      (erased (HoldsR r (Cons (Col) e et) w) h) (erased (MatchG (BS0) (Cons (Col) e et) w) m) (erased (GramRot w w1) g) -> (RotR r ct w1)))

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
        (let ((erased w1) (erased g) (erased m1)) (rot-match e et ct w mw s))
        (values w1 m1 (MkHoldsR (RelC) R RotR ct w1 (MkRotR R et ct e w w1 s rr mw g)))))
    (def-fns M
      ((erased cm1 : (erased (List (Col)) ct ct2) (erased (List (Gsym)) w1) (erased (HoldsR R1 ct w1) r) (erased (MatchG (BS0) ct2 w1) m) ->
          (erased (Holds P1 ct2) q))
        (let-match erased r (MkHoldsR _ _ _ _ _ h))
        (let-match erased h (MkRotR _ et _ e w _ s rr mw g))
        (let ((erased e2) (erased et2) (erased s2) (erased mw2)) (rot-unmatch w w1 ct2 (Cons _ e et) g m mw))
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
