; The corner after dart d, with the active items there, in sweep order.
(def-adts $ (Group : -> Type)
  enum
  (many MkGroup : (many (Nat) d) (many (List (Nat)) items) -> (Group)))

(def-adts $ (Darts : ((List (Group)) gs) ((List (Nat)) s) -> Type)
  enum
  (many DartsNil : -> (Darts (Nil (Group)) (Nil (Nat))))
  (many DartsCons : (erased (Nat) d) (erased (List (Nat)) xs s) (erased (List (Group)) gs) (erased (Darts gs s) p)
      -> (Darts (Cons (Group) (MkGroup d xs) gs) (Cons (Nat) d s))))

; Every element of s is outside m.
(def-adts $ (Disj : ((List (Nat)) s) ((List (Nat)) m) -> Type)
  enum
  (many DisjNil : (erased (List (Nat)) m) -> (Disj (Nil (Nat)) m))
  (many DisjCons : (erased (Nat) x) (erased (List (Nat)) s m) (erased (NotIn x m) p) (erased (Disj s m) rest)
      -> (Disj (Cons (Nat) x s) m)))

; The walk from the corner after d1 to the step into the corner after d2.
(def-adts $ (Link : ((List (Nat)) e) ((List (Nat)) nd) ((List (Nat)) s) ((Nat) d1) ((Nat) d2) -> Type)
  enum
  (many MkLink : (erased (List (Nat)) e nd s) (erased (Nat) d1 d2 c p)
      (erased (Nth (Nat) nd d1 c) pc) (erased (Nth (Nat) e d2 p) pp) (erased (Walk e nd s c p) w)
      -> (Link e nd s d1 d2)))

; The groups gs linked one after another, the last one to the corner after dn.
(def-adts $ (Chain : ((List (Nat)) e) ((List (Nat)) nd) ((List (Nat)) s) ((List (Group)) gs) ((Nat) dn) -> Type)
  enum
  (many ChainOne : (erased (List (Nat)) e nd s xs) (erased (Nat) d dn) (erased (Link e nd s d dn) k)
      -> (Chain e nd s (Cons (Group) (MkGroup d xs) (Nil (Group))) dn))
  (many ChainCons : (erased (List (Nat)) e nd s xs ys) (erased (List (Group)) gs) (erased (Nat) d d2 dn)
      (erased (Link e nd s d d2) k) (erased (Chain e nd s (Cons (Group) (MkGroup d2 ys) gs) dn) rest)
      -> (Chain e nd s (Cons (Group) (MkGroup d xs) (Cons (Group) (MkGroup d2 ys) gs)) dn)))

(def-fns _ $ (erased disj-notin : (erased (Nat) x) (erased (List (Nat)) s m) (subterm erased (Disj s m) dj) (erased (In x s) p) ->
    (erased (NotIn x m) r))
  (let-match erased dj (DisjCons y s1 _ q dj1) (absurd (DisjNil _) p))
  (let-match erased p (InThere _ _ _ p1) ((InHere _ _) q))
  (disj-notin x s1 m dj1 p1))

(def-fns _ $ (erased link-move : (erased (List (Nat)) e nd e2 nd2 s s2 m) (erased (Nat) d1 d2 n) (erased (Link e nd s d1 d2) k)
    (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) l) (erased (SubFresh s2 s n) sf)
    (erased (Agree e e2 (Nil (Nat))) ge) (erased (Agree nd nd2 m) gn) (erased (Sub m s) sb) (erased (NotIn d1 m) keep)
    -> (erased (Link e2 nd2 s2 d1 d2) r))
  (let-match erased k (MkLink _ _ _ _ _ c p pc pp w))
  (MkLink e2 nd2 s2 d1 d2 c p (agree-nth nd nd2 m d1 c gn pc keep) (agree-nth e e2 (Nil (Nat)) d2 p ge pp (NotInNil d2))
    (walk-move e nd e2 nd2 s s2 m c p n w pm l sf ge gn sb)))

(def-fns _ $ (erased chain-move : (erased (List (Nat)) e nd e2 nd2 s s2 m sg) (erased (List (Group)) gs) (erased (Nat) dn n)
    (subterm erased (Chain e nd s gs dn) ch) (erased (Darts gs sg) ds) (erased (Disj sg m) dj)
    (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) l) (erased (SubFresh s2 s n) sf)
    (erased (Agree e e2 (Nil (Nat))) ge) (erased (Agree nd nd2 m) gn) (erased (Sub m s) sb)
    -> (erased (Chain e2 nd2 s2 gs dn) r))
  (match erased ch _
    ((ChainOne _ _ _ xs d _ k)
      (let-match erased ds (DartsCons _ _ _ _ _))
      (ChainOne e2 nd2 s2 xs d dn
        (link-move e nd e2 nd2 s s2 m d dn n k pm l sf ge gn sb (disj-notin d sg m dj (InHere d _)))))
    ((ChainCons _ _ _ xs ys gs1 d d2 _ k rest)
      (let-match erased ds (DartsCons _ _ sg1 _ ds1))
      (let-match erased dj (DisjCons _ _ _ keep dj1))
      (ChainCons e2 nd2 s2 xs ys gs1 d d2 dn
        (link-move e nd e2 nd2 s s2 m d d2 n k pm l sf ge gn sb keep)
        (chain-move e nd e2 nd2 s s2 m sg1 (Cons _ (MkGroup d2 ys) gs1) dn n rest ds1 dj1 pm l sf ge gn sb)))))

(def-fns _ $ (erased link-rehead : (erased (List (Nat)) e nd e2 nd2 s s2 m) (erased (Nat) d1 x d2 n c0) (erased (Link e nd s d1 d2) k)
    (erased (Nth (Nat) nd d1 c0) old) (erased (Nth (Nat) nd2 x c0) new)
    (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) l) (erased (SubFresh s2 s n) sf)
    (erased (Agree e e2 (Nil (Nat))) ge) (erased (Agree nd nd2 m) gn) (erased (Sub m s) sb)
    -> (erased (Link e2 nd2 s2 x d2) r))
  (let-match erased k (MkLink _ _ _ _ _ c p pc pp w))
  (let-match erased (nth-fn _ nd d1 c c0 pc old) (Refl _ _))
  (MkLink e2 nd2 s2 x d2 c p new (agree-nth e e2 (Nil (Nat)) d2 p ge pp (NotInNil d2))
    (walk-move e nd e2 nd2 s s2 m c p n w pm l sf ge gn sb)))

; The head group's corner moves from the corner after d to the corner after x.
(def-fns _ $ (erased chain-rehead : (erased (List (Nat)) e nd e2 nd2 s s2 m sg xs xs2) (erased (List (Group)) gs) (erased (Nat) d x dn n c0)
    (erased (Chain e nd s (Cons (Group) (MkGroup d xs) gs) dn) ch) (erased (Darts gs sg) ds) (erased (Disj sg m) dj)
    (erased (Nth (Nat) nd d c0) old) (erased (Nth (Nat) nd2 x c0) new)
    (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) l) (erased (SubFresh s2 s n) sf)
    (erased (Agree e e2 (Nil (Nat))) ge) (erased (Agree nd nd2 m) gn) (erased (Sub m s) sb)
    -> (erased (Chain e2 nd2 s2 (Cons (Group) (MkGroup x xs2) gs) dn) r))
  (match erased ch _
    ((ChainOne _ _ _ _ _ _ k) (ChainOne e2 nd2 s2 xs2 x dn (link-rehead e nd e2 nd2 s s2 m d x dn n c0 k old new pm l sf ge gn sb)))
    ((ChainCons _ _ _ _ ys gs1 _ d2 _ k rest)
      (ChainCons e2 nd2 s2 xs2 ys gs1 x d2 dn (link-rehead e nd e2 nd2 s s2 m d x d2 n c0 k old new pm l sf ge gn sb)
        (chain-move e nd e2 nd2 s s2 m sg gs dn n rest ds dj pm l sf ge gn sb)))))

(def-fns _ $ (erased notin-disj : (erased (Nat) a b) (erased (List (Nat)) s) (subterm erased (NotIn a s) pa) (erased (NotIn b s) pb) ->
    (erased (Disj s (Cons (Nat) a $ Cons (Nat) b $ Nil (Nat))) r))
  (let-match erased pa (NotInCons _ x s1 na pa1) ((NotInNil _) (DisjNil _)))
  (let-match erased pb (NotInCons _ _ _ nb pb1))
  (DisjCons x s1 _ (NotInCons x a _ (apart-sym a x na) $ NotInCons x b _ (apart-sym b x nb) $ NotInNil x) (notin-disj a b s1 pa1 pb1)))

(def-fns _ $ (erased grow-agree : (erased (List (Nat)) e e2) (erased (Nat) n) (erased (EdgeGrow e n e2) g) ->
    (erased (Agree e e2 (Nil (Nat))) r))
  (let-match erased g (MkEdgeGrow _ e1 _ _ _ s1 s2))
  (AgTrans e e1 e2 (Nil _) (AgSnoc e e1 (Nil _) (Succ n) s1) (AgSnoc e1 e2 (Nil _) n s2)))

(def-fns _ $ (erased chain-head : (erased (List (Nat)) e nd s xs) (erased (List (Group)) gs) (erased (Nat) d dn)
    (erased (Chain e nd s (Cons (Group) (MkGroup d xs) gs) dn) ch) -> (erased (Nat) c) (erased (Nth (Nat) nd d c) p))
  (match erased ch _
    ((ChainOne _ _ _ _ _ _ k) (let-match erased k (MkLink _ _ _ _ _ c _ pc _ _)) (values c pc))
    ((ChainCons _ _ _ _ _ _ _ _ _ k _) (let-match erased k (MkLink _ _ _ _ _ c _ pc _ _)) (values c pc))))

; One more edge from v: the corner after y1 at v is joined to the corner after c, where the next closed item sits.
(def-fns _ $ (erased chord-step : (erased (List (Nat)) e nd sr pl xb ya xc yb xc2) (erased (List (Group)) rest) (erased (Nat) n db y1 c v u)
    (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) l) (erased (Length (Nat) nd n) ln)
    (erased (Chain e nd (Cons (Nat) db $ Cons (Nat) y1 $ Cons (Nat) c sr)
      (Cons (Group) (MkGroup db xb) $ Cons (Group) (MkGroup y1 ya) $ Cons (Group) (MkGroup c xc) rest) db) ch)
    (erased (Darts rest sr) ds) (erased (Distinct (Cons (Nat) db $ Cons (Nat) y1 $ Cons (Nat) c sr)) dist)
    (erased (Respects pl nd pl) rp) (erased (Nth (Nat) pl y1 v) pv) (erased (Nth (Nat) pl c u) pu) (erased (Apart (Nat) Lt v u) vu)
    -> (erased (List (Nat)) e2 nd1 nd2) (erased (EdgeGrow e n e2) g) (erased (Insert nd y1 n nd1) i1) (erased (Insert nd1 c (Succ n) nd2) i2)
    (erased (PlaneMap e2 nd2) pm2)
    (erased (Chain e2 nd2 (Cons (Nat) db $ Cons (Nat) y1 $ Cons (Nat) (Succ n) sr)
      (Cons (Group) (MkGroup db xb) $ Cons (Group) (MkGroup y1 yb) $ Cons (Group) (MkGroup (Succ n) xc2) rest) db) ch2))
  (let ((erased s)) (Cons (Nat) db $ Cons (Nat) y1 $ Cons (Nat) c sr))
  (let ((erased s2)) (Cons (Nat) db $ Cons (Nat) y1 $ Cons (Nat) (Succ n) sr))
  (let ((erased m)) (Cons (Nat) y1 $ Cons (Nat) c $ Nil (Nat)))
  (let-match erased ch (ChainCons _ _ _ _ _ _ _ _ _ k0 ch1))
  (let-match erased ch1 (ChainCons _ _ _ _ _ _ _ _ _ k1 ch3))
  (let-match erased k1 (MkLink _ _ _ _ _ c1 p1 pc1 pp1 w1))
  (let ((erased c2) (erased pc2)) (chain-head e nd s xc rest c db ch3))
  (let-match erased dist (DistCons _ _ ndb dist1))
  (let-match erased dist1 (DistCons _ _ ny1 dist2))
  (let-match erased dist2 (DistCons _ _ nc _))
  (let ((erased db-y1) (erased ndb1)) (notin-head db y1 _ ndb))
  (let ((erased db-c) (erased _)) (notin-head db c _ ndb1))
  (let ((erased y1-c) (erased ny1r)) (notin-head y1 c _ ny1))
  (let ((erased c-y1)) (apart-sym y1 c y1-c))
  (let ((erased nd1) (erased i1)) (insert-exists nd y1 n c1 pc1))
  (let ((erased pc2b)) (insert-other nd nd1 y1 n c c2 i1 pc2 c-y1))
  (let ((erased nd2) (erased i2)) (insert-exists nd1 c (Succ n) c2 pc2b))
  (let ((erased e2) (erased g)) (grow-exists e n l))
  (let ((erased join)) (JoinFace e nd y1 c c1 c2 pc1 pc2
    (fr-snoc e nd c1 p1 c c2 (walk-face e nd s c1 p1 w1) (pm-edge-inv e nd c p1 pm pp1) pc2)))
  (let ((erased pm2)) (PMChord e nd e2 nd1 nd2 pl n y1 c pm g (nth-lt-length _ nd y1 n c1 pc1 ln) (nth-lt-length _ nd c n c2 pc2 ln)
    (MkSeparates pl nd y1 c v u rp pv pu vu) join i1 i2))
  (let ((erased ge)) (grow-agree e e2 n g))
  (let ((erased gn)) (AgTrans nd nd1 nd2 m (AgInsert nd nd1 m y1 n i1 (InHere y1 _)) (AgInsert nd1 nd2 m c (Succ n) i2 (InThere c y1 _ (InHere c _)))))
  (let ((erased sb)) (SubCons y1 _ s (InThere y1 db _ (InHere y1 _)) $ SubCons c _ s (InThere c db _ $ InThere c y1 _ $ InHere c _) $ SubNil s))
  (let ((erased sf)) (SFOld db n _ s (InHere db _) $ SFOld y1 n _ s (InThere y1 db _ (InHere y1 _)) $
    SFNew (Succ n) n sr s (lt-weaken n (Succ n) (lt-succ n))
    (sf-of-sub sr s n (sub-cons db sr _ $ sub-cons y1 sr _ $ sub-cons c sr sr $ sub-refl sr))))
  (let ((erased k0b)) (link-move e nd e2 nd2 s s2 m db y1 n k0 pm l sf ge gn sb (NotInCons db y1 _ db-y1 $ NotInCons db c _ db-c $ NotInNil db)))
  (let ((erased k1b)) (MkLink e2 nd2 s2 y1 (Succ n) n n (insert-other nd1 nd2 c (Succ n) y1 n i2 (insert-at nd nd1 y1 n i1) y1-c)
    (edge-high e e2 n g) (WalkHere e2 nd2 s2 n)))
  (let ((erased ch4)) (chain-rehead e nd e2 nd2 s s2 m sr xc xc2 rest c (Succ n) db n c2 ch3 ds (notin-disj y1 c sr ny1r nc)
    pc2 (insert-new nd1 nd2 c (Succ n) (Succ n) c2 i2 (insert-length nd nd1 y1 n n i1 ln) pc2b) pm l sf ge gn sb))
  (values e2 nd1 nd2 g i1 i2 pm2
    (ChainCons e2 nd2 s2 xb yb _ db y1 db k0b (ChainCons e2 nd2 s2 yb xc2 rest y1 (Succ n) db k1b ch4))))

(def-fns _ $ (erased notin-disj1 : (erased (Nat) a) (erased (List (Nat)) s) (subterm erased (NotIn a s) pa) ->
    (erased (Disj s (Cons (Nat) a $ Nil (Nat))) r))
  (let-match erased pa (NotInCons _ x s1 na pa1) ((NotInNil _) (DisjNil _)))
  (DisjCons x s1 _ (NotInCons x a _ (apart-sym a x na) $ NotInNil x) (notin-disj1 a s1 pa1)))

; The first edge from v: a pendant at the corner after d, the head group's dart; v's only dart is n+1.
(def-fns _ $ (erased pendant-step : (erased (List (Nat)) e nd sr xs xb ys xc) (erased (List (Group)) rest) (erased (Nat) n d)
    (erased (PlaneMap e nd) pm) (erased (Length (Nat) e n) l) (erased (Length (Nat) nd n) ln)
    (erased (Chain e nd (Cons (Nat) d sr) (Cons (Group) (MkGroup d xs) rest) d) ch)
    (erased (Darts rest sr) ds) (erased (Distinct (Cons (Nat) d sr)) dist)
    -> (erased (List (Nat)) e2 nd1 nd2) (erased (EdgeGrow e n e2) g) (erased (Insert nd d n nd1) i1)
    (erased (Snoc (Nat) nd1 (Succ n) nd2) sn) (erased (PlaneMap e2 nd2) pm2)
    (erased (Chain e2 nd2 (Cons (Nat) d $ Cons (Nat) (Succ n) $ Cons (Nat) n sr)
      (Cons (Group) (MkGroup d xb) $ Cons (Group) (MkGroup (Succ n) ys) $ Cons (Group) (MkGroup n xc) rest) d) ch2))
  (let ((erased s)) (Cons (Nat) d sr))
  (let ((erased s2)) (Cons (Nat) d $ Cons (Nat) (Succ n) $ Cons (Nat) n sr))
  (let ((erased m)) (Cons (Nat) d $ Nil (Nat)))
  (let ((erased c) (erased pc)) (chain-head e nd s xs rest d d ch))
  (let ((erased nd1) (erased i1)) (insert-exists nd d n c pc))
  (let ((erased ln1)) (insert-length nd nd1 d n n i1 ln))
  (let ((erased nd2) (erased sn)) (snoc-exists _ nd1 (Succ n)))
  (let ((erased e2) (erased g)) (grow-exists e n l))
  (let ((erased pm2)) (PMPendant e nd e2 nd1 nd2 n d pm g (nth-lt-length _ nd d n c pc ln) i1 sn))
  (let-match erased dist (DistCons _ _ nd0 _))
  (let ((erased ge)) (grow-agree e e2 n g))
  (let ((erased gn)) (AgTrans nd nd1 nd2 m (AgInsert nd nd1 m d n i1 (InHere d _)) (AgSnoc nd1 nd2 m (Succ n) sn)))
  (let ((erased sb)) (SubCons d _ s (InHere d _) $ SubNil s))
  (let ((erased sf)) (SFOld d n _ s (InHere d _) $ SFNew (Succ n) n _ s (lt-weaken n (Succ n) (lt-succ n)) $
    SFNew n n sr s (lt-succ n) (sf-of-sub sr s n (sub-cons d sr sr $ sub-refl sr))))
  (let ((erased k0)) (MkLink e2 nd2 s2 d (Succ n) n n (snoc-old _ nd1 nd2 (Succ n) n d sn (insert-at nd nd1 d n i1))
    (edge-high e e2 n g) (WalkHere e2 nd2 s2 n)))
  (let ((erased k1)) (MkLink e2 nd2 s2 (Succ n) n (Succ n) (Succ n) (snoc-new _ nd1 nd2 (Succ n) (Succ n) sn ln1)
    (edge-low e e2 n g) (WalkHere e2 nd2 s2 (Succ n))))
  (let ((erased ch3)) (chain-rehead e nd e2 nd2 s s2 m sr xs xc rest d n d n c ch ds (notin-disj1 d sr nd0)
    pc (snoc-old _ nd1 nd2 (Succ n) c n sn (insert-new nd nd1 d n n c i1 ln pc)) pm l sf ge gn sb))
  (values e2 nd1 nd2 g i1 sn pm2
    (ChainCons e2 nd2 s2 xb ys _ d (Succ n) d k0 (ChainCons e2 nd2 s2 ys xc rest (Succ n) n d k1 ch3))))
