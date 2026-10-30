; The cube construction of Gonthier's cube.v: from a hypermap on d darts, a plain cubic hypermap on 6 d darts, laid out
; as six blocks of d darts, of the same genus, bridgeless when the map is, and whose four-colourings give four-colourings
; of the map.

(let ((erased tg1)) (Succ (Zero)))
(let ((erased tg2)) (Succ tg1))
(let ((erased tg3)) (Succ tg2))
(let ((erased tg4)) (Succ tg3))
(let ((erased tg5)) (Succ tg4))
(let ((erased tg6)) (Succ tg5))

; z = t d + x: z is dart x of block t.
(def-adts $ (At : ((Nat) d t x z) -> Type)
  enum
  (many AtZ : (erased (Nat) d x) -> (At d (Zero) x x))
  (many AtS : (erased (Nat) d t x z z2) (erased (At d t x z) p) (erased (Add d z z2) a) -> (At d (Succ t) x z2)))

; A block of a list over the darts of a cube: dart x of the block goes to dart (p x) of block o.
(def-adts $ (Blk : -> Type)
  enum
  (many MkBlk : (many (Nat) o) (many (List (Nat)) p) -> (Blk)))

; b sends position i to dart (p i) of block o.
(def-adts $ (Shf : ((Nat) d o) ((List (Nat)) p b) -> Type)
  enum
  (many ShfNil : (erased (Nat) d o) -> (Shf d o (Nil (Nat)) (Nil (Nat))))
  (many ShfCons : (erased (Nat) d o y z) (erased (List (Nat)) p b) (erased (At d o y z) a) (erased (Shf d o p b) rest)
      -> (Shf d o (Cons (Nat) y p) (Cons (Nat) z b))))

; zs is xs followed by ys.
(def-adts $ (Join : ((List (Nat)) xs ys zs) -> Type)
  enum
  (many JoinNil : (erased (List (Nat)) ys) -> (Join (Nil (Nat)) ys ys))
  (many JoinCons : (erased (List (Nat)) xs ys zs) (erased (Nat) x) (erased (Join xs ys zs) p)
      -> (Join (Cons (Nat) x xs) ys (Cons (Nat) x zs))))

; xs is the blocks of s, one after another.
(def-adts $ (Lay : ((Nat) d) ((List (Blk)) s) ((List (Nat)) xs) -> Type)
  enum
  (many LayNil : (erased (Nat) d) -> (Lay d (Nil (Blk)) (Nil (Nat))))
  (many LayCons : (erased (Nat) d o) (erased (List (Nat)) p b rest xs) (erased (List (Blk)) s) (erased (Shf d o p b) sh)
      (erased (Join b rest xs) ap) (erased (Lay d s rest) ly) -> (Lay d (Cons (Blk) (MkBlk o p) s) xs)))

; Every block of s has d darts.
(def-adts $ (Sized : ((Nat) d) ((List (Blk)) s) -> Type)
  enum
  (many SizedNil : (erased (Nat) d) -> (Sized d (Nil (Blk))))
  (many SizedCons : (erased (Nat) d o) (erased (List (Nat)) p) (erased (List (Blk)) s) (erased (Length (Nat) p d) lp) (erased (Sized d s) rest)
      -> (Sized d (Cons (Blk) (MkBlk o p) s))))

(def-fns _ $ (erased add-mono : (erased (Nat) a b c b2 c2) (subterm erased (Add a b c) p) (erased (Add a b2 c2) q) (erased (Lt b b2) l)
    -> (erased (Lt c c2) r))
  (let-match erased p (AddSucc a1 _ c1 p1) ((AddZero _) (let-match erased q (AddZero _)) l))
  (let-match erased q (AddSucc _ _ c3 q1))
  (LtS c1 c3 (add-mono a1 b c1 b2 c3 p1 q1 l)))

(def-fns _ $ (erased at-fn : (erased (Nat) d t x z z2) (subterm erased (At d t x z) p) (erased (At d t x z2) q) -> (erased (Eq (Nat) z z2) e))
  (let-match erased p (AtS _ t1 _ w _ p1 a) ((AtZ _ _) (let-match erased q (AtZ _ _)) (Refl _ z)))
  (let-match erased q (AtS _ _ _ w2 _ q1 b))
  (let-match erased (at-fn d t1 x w w2 p1 q1) (Refl _ _))
  (add-fn d w z z2 a b))

(def-fns _ $ (erased at-exists : (erased (Nat) d) (subterm erased (Nat) t) (erased (Nat) x) -> (erased (Nat) z) (erased (At d t x z) p))
  (let-match erased t (Succ t1) ((Zero) (values x (AtZ d x))))
  (let ((erased z1) (erased p1)) (at-exists d t1 x))
  (let ((erased z) (erased a)) (add d z1))
  (values z (AtS d t1 x z1 z p1 a)))

; A dart of block t lies below the first dart of any later block.
(def-fns _ $ (erased at-lt : (erased (Nat) d t x z t2 w) (erased (At d t x z) p) (subterm erased (At d t2 (Zero) w) q) (erased (Lt x d) lx)
    (erased (Lt t t2) lt) -> (erased (Lt z w) r))
  (let-match erased q (AtS _ t3 _ w3 _ q1 b) (absurd (AtZ _ _) lt))
  (let-match erased p (AtS _ t1 _ z1 _ p1 a) ((AtZ _ _) (lt-le-trans x d w lx (add-le-left d w3 w b))))
  (let-match erased lt (LtS _ _ lt1))
  (add-mono d z1 z w3 w a b (at-lt d t1 x z1 t3 w3 p1 q1 lx lt1)))

; The block and the position of a dart are determined.
(def-fns _ $ (erased at-inj : (erased (Nat) d t x z t2 x2) (subterm erased (At d t x z) p) (erased (At d t2 x2 z) q) (erased (Lt x d) lx)
    (erased (Lt x2 d) lx2) -> (erased (Eq (Nat) t t2) e1) (erased (Eq (Nat) x x2) e2))
  (let-match erased p (AtS _ t1 _ z1 _ p1 a)
    ((AtZ _ _)
      (let-match erased q (AtZ _ _) (absurd (AtS _ _ _ z2 _ _ b) (lt-asym x d lx (add-le-left d z2 x b))))
      (values (Refl _ t) (Refl _ x))))
  (let-match erased q (AtS _ t3 _ z3 _ q1 b) (absurd (AtZ _ _) (lt-asym x2 d lx2 (add-le-left d z1 x2 a))))
  (let-match erased (add-cancel d z1 z3 z a b) (Refl _ _))
  (let ((erased e1) (erased e2)) (at-inj d t1 x z1 t3 x2 p1 q1 lx lx2))
  (values (eq-cong-succ t1 t3 e1) e2))

; Darts of different blocks, or at different positions, differ.
(def-fns _ $ (erased at-apart : (erased (Nat) d t x z t2 x2 z2) (erased (At d t x z) p) (erased (At d t2 x2 z2) q) (erased (Lt x d) lx)
    (erased (Lt x2 d) lx2) (erased (Or (Apart (Nat) Lt t t2) (Apart (Nat) Lt x x2)) o) -> (erased (Apart (Nat) Lt z z2) r))
  (let-match erased (nat-eq z z2) (Unequal _ _ _ _ ne)
    (absurd (Equal _ _ _)
      (let ((erased e1) (erased e2)) (at-inj d t x z t2 x2 p q lx lx2))
      (let-match erased e1 (Refl _ _))
      (let-match erased e2 (Refl _ _))
      (match erased o _ (absurd (OrL _ _ a) (apart-irrefl t a)) (absurd (OrR _ _ a) (apart-irrefl x a)))))
  ne)

(def-adts $ (JoinAt : ((List (Nat)) b r) ((Nat) k j w) -> Type)
  enum
  (many JALeft : (erased (List (Nat)) b r) (erased (Nat) k j w) (erased (Lt j k) l) (erased (Nth (Nat) b j w) p) -> (JoinAt b r k j w))
  (many JARight : (erased (List (Nat)) b r) (erased (Nat) k j w i) (erased (Add k i j) a) (erased (Nth (Nat) r i w) p) -> (JoinAt b r k j w)))

(def-fns _ $ (erased join-nth-l : (erased (List (Nat)) b r xs) (erased (Nat) i w) (subterm erased (Join b r xs) ap) (erased (Nth (Nat) b i w) p)
    -> (erased (Nth (Nat) xs i w) q))
  (let-match erased ap (JoinCons b1 _ xs1 x ap1) (absurd (JoinNil _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p1) ((NthHere _ _ _) (NthHere _ x xs1)))
  (NthThere _ x xs1 i1 w (join-nth-l b1 r xs1 i1 w ap1 p1)))

(def-fns _ $ (erased join-nth-r : (erased (List (Nat)) b r xs) (erased (Nat) k i j w) (subterm erased (Join b r xs) ap) (erased (Length (Nat) b k) lb)
    (erased (Add k i j) a) (erased (Nth (Nat) r i w) p) -> (erased (Nth (Nat) xs j w) q))
  (let-match erased ap (JoinCons b1 _ xs1 x ap1)
    ((JoinNil _) (let-match erased lb (LengthNil _)) (let-match erased a (AddZero _)) p))
  (let-match erased lb (LengthCons _ _ _ k1 lb1))
  (let-match erased a (AddSucc _ _ j1 a1))
  (NthThere _ x xs1 j1 w (join-nth-r b1 r xs1 k1 i j1 w ap1 lb1 a1 p)))

(def-fns _ $ (erased join-nth-inv : (erased (List (Nat)) b r xs) (erased (Nat) k j w) (subterm erased (Join b r xs) ap) (erased (Length (Nat) b k) lb)
    (erased (Nth (Nat) xs j w) p) -> (erased (JoinAt b r k j w) res))
  (let-match erased ap (JoinCons b1 _ xs1 x ap1)
    ((JoinNil _) (let-match erased lb (LengthNil _)) (JARight b r k j w j (AddZero j) p)))
  (let-match erased lb (LengthCons _ _ _ k1 lb1))
  (let-match erased p (NthThere _ _ _ j1 _ p1) ((NthHere _ _ _) (JALeft b r k j w (LtZ k1) (NthHere _ x b1))))
  (match erased (join-nth-inv b1 r xs1 k1 j1 w ap1 lb1 p1) _
    ((JALeft _ _ _ _ _ l q) (JALeft b r k j w (LtS j1 k1 l) (NthThere _ x b1 j1 w q)))
    ((JARight _ _ _ _ _ i a q) (JARight b r k j w i (AddSucc k1 i j1 a) q))))

(def-fns _ $ (erased join-length : (erased (List (Nat)) b r xs) (erased (Nat) k m km) (subterm erased (Join b r xs) ap) (erased (Length (Nat) b k) lb)
    (erased (Length (Nat) r m) lr) (erased (Add k m km) a) -> (erased (Length (Nat) xs km) res))
  (let-match erased ap (JoinCons b1 _ xs1 x ap1)
    ((JoinNil _) (let-match erased lb (LengthNil _)) (let-match erased a (AddZero _)) lr))
  (let-match erased lb (LengthCons _ _ _ k1 lb1))
  (let-match erased a (AddSucc _ _ km1 a1))
  (LengthCons _ x xs1 km1 (join-length b1 r xs1 k1 m km1 ap1 lb1 lr a1)))

(def-fns _ $ (erased join-exists : (subterm erased (List (Nat)) b) (erased (List (Nat)) r) -> (erased (List (Nat)) xs) (erased (Join b r xs) ap))
  (let-match erased b (Cons _ x b1) ((Nil _) (values r (JoinNil r))))
  (let ((erased xs1) (erased ap1)) (join-exists b1 r))
  (values (Cons _ x xs1) (JoinCons b1 r xs1 x ap1)))

(def-fns _ $ (erased shf-nth : (erased (Nat) d o x y w) (erased (List (Nat)) p b) (subterm erased (Shf d o p b) sh) (erased (Nth (Nat) p x y) px)
    (erased (At d o y w) a) -> (erased (Nth (Nat) b x w) r))
  (let-match erased sh (ShfCons _ _ y1 z p1 b1 a1 sh1) (absurd (ShfNil _ _) px))
  (let-match erased px (NthThere _ _ _ x1 _ px1)
    ((NthHere _ _ _) (let-match erased (at-fn d o y z w a1 a) (Refl _ _)) (NthHere _ z b1)))
  (NthThere _ z b1 x1 w (shf-nth d o x1 y w p1 b1 sh1 px1 a)))

(def-fns _ $ (erased shf-nth-inv : (erased (Nat) d o x w) (erased (List (Nat)) p b) (subterm erased (Shf d o p b) sh) (erased (Nth (Nat) b x w) pb)
    -> (erased (Nat) y) (erased (Nth (Nat) p x y) px) (erased (At d o y w) a))
  (let-match erased sh (ShfCons _ _ y1 z p1 b1 a1 sh1) (absurd (ShfNil _ _) pb))
  (let-match erased pb (NthThere _ _ _ x1 _ pb1) ((NthHere _ _ _) (values y1 (NthHere _ y1 p1) a1)))
  (let ((erased y) (erased px) (erased a)) (shf-nth-inv d o x1 w p1 b1 sh1 pb1))
  (values y (NthThere _ y1 p1 x1 y px) a))

(def-fns _ $ (erased shf-length : (erased (Nat) d o k) (erased (List (Nat)) p b) (subterm erased (Shf d o p b) sh) (erased (Length (Nat) p k) lp)
    -> (erased (Length (Nat) b k) r))
  (let-match erased sh (ShfCons _ _ y z p1 b1 a sh1) ((ShfNil _ _) (let-match erased lp (LengthNil _)) (LengthNil _)))
  (let-match erased lp (LengthCons _ _ _ k1 lp1))
  (LengthCons _ z b1 k1 (shf-length d o k1 p1 b1 sh1 lp1)))

(def-fns _ $ (erased shf-exists : (erased (Nat) d o) (subterm erased (List (Nat)) p) -> (erased (List (Nat)) b) (erased (Shf d o p b) sh))
  (let-match erased p (Cons _ y p1) ((Nil _) (values (Nil _) (ShfNil d o))))
  (let ((erased z) (erased a)) (at-exists d o y))
  (let ((erased b1) (erased sh1)) (shf-exists d o p1))
  (values (Cons _ z b1) (ShfCons d o y z p1 b1 a sh1)))

(def-fns _ $ (erased lay-exists : (erased (Nat) d) (subterm erased (List (Blk)) s) -> (erased (List (Nat)) xs) (erased (Lay d s xs) ly))
  (let-match erased s (Cons _ bk s1) ((Nil _) (values (Nil _) (LayNil d))))
  (let-match erased bk (MkBlk o p))
  (let ((erased b) (erased sh)) (shf-exists d o p))
  (let ((erased rest) (erased ly1)) (lay-exists d s1))
  (let ((erased xs) (erased ap)) (join-exists b rest))
  (values xs (LayCons d o p b rest xs s1 sh ap ly1)))

(def-fns _ $ (erased lay-nth : (erased (Nat) d t o x y z w) (erased (List (Blk)) s) (erased (List (Nat)) p xs) (erased (Lay d s xs) ly)
    (erased (Sized d s) sz) (subterm erased (Nth (Blk) s t (MkBlk o p)) ps) (erased (Nth (Nat) p x y) px) (erased (At d t x z) az)
    (erased (At d o y w) aw) -> (erased (Nth (Nat) xs z w) r))
  (let-match erased ly (LayCons _ o0 p0 b rest _ s1 sh ap ly1) (absurd (LayNil _) ps))
  (let-match erased sz (SizedCons _ _ _ _ lp sz1))
  (let-match erased ps (NthThere _ _ _ t1 _ ps1)
    ((NthHere _ _ _) (let-match erased az (AtZ _ _)) (join-nth-l b rest xs x w ap (shf-nth d o x y w p b sh px aw))))
  (let-match erased az (AtS _ _ _ z1 _ az1 a))
  (join-nth-r b rest xs d z1 z w ap (shf-length d o0 d p0 b sh lp) a (lay-nth d t1 o x y z1 w s1 p rest ly1 sz1 ps1 px az1 aw)))

; Every entry of a laid-out list is dart (p x) of block o for the block t and position x it is at.
(def-fns _ $ (erased lay-nth-inv : (erased (Nat) d z w) (erased (List (Blk)) s) (erased (List (Nat)) xs) (subterm erased (Lay d s xs) ly)
    (erased (Sized d s) sz) (erased (Nth (Nat) xs z w) pz)
    -> (erased (Nat) t o) (erased (List (Nat)) p) (erased (Nat) x y) (erased (Nth (Blk) s t (MkBlk o p)) ps) (erased (Nth (Nat) p x y) px)
    (erased (At d t x z) az) (erased (At d o y w) aw) (erased (Lt x d) lx))
  (let-match erased ly (LayCons _ o0 p0 b rest _ s1 sh ap ly1) (absurd (LayNil _) pz))
  (let-match erased sz (SizedCons _ _ _ _ lp sz1))
  (match erased (join-nth-inv b rest xs d z w ap (shf-length d o0 d p0 b sh lp) pz) _
    ((JALeft _ _ _ _ _ l q)
      (let ((erased y) (erased px) (erased aw)) (shf-nth-inv d o0 z w p0 b sh q))
      (values (Zero) o0 p0 z y (NthHere _ (MkBlk o0 p0) s1) px (AtZ d z) aw l))
    ((JARight _ _ _ _ _ i a q)
      (let ((erased t) (erased o) (erased p) (erased x) (erased y) (erased ps) (erased px) (erased az) (erased aw) (erased lx))
        (lay-nth-inv d i w s1 rest ly1 sz1 q))
      (values (Succ t) o p x y (NthThere _ (MkBlk o0 p0) s1 t (MkBlk o p) ps) px (AtS d t x i z az a) aw lx))))

(def-fns _ $ (erased lay-length : (erased (Nat) d m D) (erased (List (Blk)) s) (erased (List (Nat)) xs) (subterm erased (Lay d s xs) ly)
    (erased (Sized d s) sz) (erased (Length (Blk) s m) ls) (erased (At d m (Zero) D) a) -> (erased (Length (Nat) xs D) r))
  (let-match erased ly (LayCons _ o p b rest _ s1 sh ap ly1)
    ((LayNil _) (let-match erased ls (LengthNil _)) (let-match erased a (AtZ _ _)) (LengthNil _)))
  (let-match erased sz (SizedCons _ _ _ _ lp sz1))
  (let-match erased ls (LengthCons _ _ _ m1 ls1))
  (let-match erased a (AtS _ _ _ D1 _ a1 ad))
  (join-length b rest xs d D1 D ap (shf-length d o d p b sh lp) (lay-length d m1 D1 s1 rest ly1 sz1 ls1 a1) ad))

; Block by block, the composite of the list laid out by sa after the one laid out by sb is the one laid out by sc.
(def-adts $ (LResp : ((List (Blk)) sa sb sc) -> Type)
  enum
  (many LRNil : (erased (List (Blk)) sa) -> (LResp sa (Nil (Blk)) (Nil (Blk))))
  (many LRCons : (erased (List (Blk)) sa sb sc) (erased (Nat) o o2) (erased (List (Nat)) r p q) (erased (Nth (Blk) sa o (MkBlk o2 r)) pa)
      (erased (Respects r p q) rp) (erased (LResp sa sb sc) rest)
      -> (LResp sa (Cons (Blk) (MkBlk o p) sb) (Cons (Blk) (MkBlk o2 q) sc))))

(def-fns _ $ (erased shf-respects : (erased (Nat) d o o2) (erased (List (Blk)) sa) (erased (List (Nat)) A r p q b c) (erased (Lay d sa A) ly)
    (erased (Sized d sa) sz) (erased (Nth (Blk) sa o (MkBlk o2 r)) pa) (subterm erased (Respects r p q) rp) (erased (Shf d o p b) sb)
    (erased (Shf d o2 q c) sc) -> (erased (Respects A b c) res))
  (let-match erased rp (RespCons _ p1 q1 y l pl rp1)
    ((RespNil _) (let-match erased sb (ShfNil _ _)) (let-match erased sc (ShfNil _ _)) (RespNil A)))
  (let-match erased sb (ShfCons _ _ _ z _ b1 az sb1))
  (let-match erased sc (ShfCons _ _ _ w _ c1 aw sc1))
  (RespCons A b1 c1 z w (lay-nth d o o2 y l z w sa r A ly sz pa pl az aw) (shf-respects d o o2 sa A r p1 q1 b1 c1 ly sz pa rp1 sb1 sc1)))

(def-fns _ $ (erased respects-join : (erased (List (Nat)) A b r xs c rc ys) (subterm erased (Respects A b c) p) (erased (Respects A r rc) q)
    (erased (Join b r xs) j1) (erased (Join c rc ys) j2) -> (erased (Respects A xs ys) res))
  (let-match erased p (RespCons _ b1 c1 y l pl p1)
    ((RespNil _) (let-match erased j1 (JoinNil _)) (let-match erased j2 (JoinNil _)) q))
  (let-match erased j1 (JoinCons _ _ xs1 _ j11))
  (let-match erased j2 (JoinCons _ _ ys1 _ j21))
  (RespCons A xs1 ys1 y l pl (respects-join A b1 r xs1 c1 rc ys1 p1 q j11 j21)))

(def-fns _ $ (erased lay-respects : (erased (Nat) d) (erased (List (Blk)) sa sb sc) (erased (List (Nat)) A B C) (erased (Lay d sa A) la)
    (erased (Sized d sa) sz) (erased (Lay d sb B) lb) (erased (Lay d sc C) lc) (subterm erased (LResp sa sb sc) lr) -> (erased (Respects A B C) res))
  (let-match erased lr (LRCons _ sb1 sc1 o o2 r p q pa rp lr1)
    ((LRNil _) (let-match erased lb (LayNil _)) (let-match erased lc (LayNil _)) (RespNil A)))
  (let-match erased lb (LayCons _ _ _ b rb _ _ shb jb lb1))
  (let-match erased lc (LayCons _ _ _ c rc _ _ shc jc lc1))
  (respects-join A b rb B c rc C (shf-respects d o o2 sa A r p q b c la sz pa rp shb shc) (lay-respects d sa sb1 sc1 A rb rc la sz lb1 lc1 lr1) jb jc))

; Position by position, the entries of xs and ys are joined in g.
(def-adts $ (Linked : ((List (Bond)) g) ((List (Nat)) xs ys) -> Type)
  enum
  (many LinkNil : (erased (List (Bond)) g) -> (Linked g (Nil (Nat)) (Nil (Nat))))
  (many LinkCons : (erased (List (Bond)) g) (erased (List (Nat)) xs ys) (erased (Nat) x y) (erased (Conn g x y) c) (erased (Linked g xs ys) rest)
      -> (Linked g (Cons (Nat) x xs) (Cons (Nat) y ys))))

(def-fns _ $ (erased link-refl : (erased (List (Bond)) g) (subterm erased (List (Nat)) xs) -> (erased (Linked g xs xs) r))
  (let-match erased xs (Cons _ x xs1) ((Nil _) (LinkNil g)))
  (LinkCons g xs1 xs1 x x (ConnHere g x) (link-refl g xs1)))

(def-fns _ $ (erased link-sym : (erased (List (Bond)) g) (erased (List (Nat)) xs ys) (subterm erased (Linked g xs ys) l) -> (erased (Linked g ys xs) r))
  (let-match erased l (LinkCons _ xs1 ys1 x y c l1) ((LinkNil _) (LinkNil g)))
  (LinkCons g ys1 xs1 y x (conn-sym g x y c) (link-sym g xs1 ys1 l1)))

(def-fns _ $ (erased link-trans : (erased (List (Bond)) g) (erased (List (Nat)) xs ys zs) (subterm erased (Linked g xs ys) l) (erased (Linked g ys zs) m)
    -> (erased (Linked g xs zs) r))
  (let-match erased l (LinkCons _ xs1 ys1 x y c l1) ((LinkNil _) m))
  (let-match erased m (LinkCons _ _ zs1 _ z c2 m1))
  (LinkCons g xs1 zs1 x z (conn-cat g x y z c c2) (link-trans g xs1 ys1 zs1 l1 m1)))

(def-fns _ $ (erased link-spans : (erased (List (Bond)) g h) (erased (List (Nat)) xs ys) (subterm erased (Linked g xs ys) l) (erased (Spans h g) sp)
    -> (erased (Linked h xs ys) r))
  (let-match erased l (LinkCons _ xs1 ys1 x y c l1) ((LinkNil _) (LinkNil h)))
  (LinkCons h xs1 ys1 x y (spans-conn h g x y c sp) (link-spans g h xs1 ys1 l1 sp)))

; A step along p links each dart of xs to its image.
(def-fns _ $ (erased link-step : (erased (Nat) D) (erased (List (Nat)) p xs ys) (erased (List (Bond)) g) (erased (Graph D p g) gr)
    (subterm erased (Respects p xs ys) rp) -> (erased (Linked g xs ys) r))
  (let-match erased rp (RespCons _ xs1 ys1 x y px rp1) ((RespNil _) (LinkNil g)))
  (LinkCons g xs1 ys1 x y (conn-adj g x y (graph-adj D x y p g gr px)) (link-step D p xs1 ys1 g gr rp1)))

(def-fns _ $ (erased link-join : (erased (List (Bond)) g) (erased (List (Nat)) a b r rb xs ys) (subterm erased (Linked g a b) l) (erased (Linked g r rb) m)
    (erased (Join a r xs) j1) (erased (Join b rb ys) j2) -> (erased (Linked g xs ys) res))
  (let-match erased l (LinkCons _ a1 b1 x y c l1)
    ((LinkNil _) (let-match erased j1 (JoinNil _)) (let-match erased j2 (JoinNil _)) m))
  (let-match erased j1 (JoinCons _ _ xs1 _ j11))
  (let-match erased j2 (JoinCons _ _ ys1 _ j21))
  (LinkCons g xs1 ys1 x y c (link-join g a1 b1 r rb xs1 ys1 l1 m j11 j21)))

; Each bond x-y of g has dart x of block t joined in h to dart y of block t.
(def-adts $ (Lift : ((List (Bond)) h) ((Nat) d t) ((List (Bond)) g) -> Type)
  enum
  (many LiftNil : (erased (List (Bond)) h) (erased (Nat) d t) -> (Lift h d t (Nil (Bond))))
  (many LiftCons : (erased (List (Bond)) h g) (erased (Nat) d t x y x2 y2) (erased (At d t x x2) px) (erased (At d t y y2) py)
      (erased (Conn h x2 y2) c) (erased (Lift h d t g) rest) -> (Lift h d t (Cons (Bond) (MkBond x y) g))))

(def-fns _ $ (erased adj-lift : (erased (List (Bond)) g h) (erased (Nat) d t x y x2) (subterm erased (Adj g x y) a) (erased (Lift h d t g) lf)
    (erased (At d t x x2) px) -> (erased (Nat) y2) (erased (At d t y y2) py) (erased (Conn h x2 y2) c))
  (match erased a _
    ((AdjFwd _ _ _)
      (let-match erased lf (LiftCons _ _ _ _ _ _ u v pu pv c _))
      (let-match erased (at-fn d t x u x2 pu px) (Refl _ _))
      (values v pv c))
    ((AdjBwd _ _ _)
      (let-match erased lf (LiftCons _ _ _ _ _ _ u v pu pv c _))
      (let-match erased (at-fn d t x v x2 pv px) (Refl _ _))
      (values u pu (conn-sym h u v c)))
    ((AdjThere g1 _ _ _ a1)
      (let-match erased lf (LiftCons _ _ _ _ _ _ _ _ _ _ _ lf1))
      (adj-lift g1 h d t x y x2 a1 lf1 px))))

(def-fns _ $ (erased conn-lift : (erased (List (Bond)) g h) (erased (Nat) d t x y x2 y2) (subterm erased (Conn g x y) c) (erased (Lift h d t g) lf)
    (erased (At d t x x2) px) (erased (At d t y y2) py) -> (erased (Conn h x2 y2) r))
  (let-match erased c (ConnStep _ _ w _ a c1)
    ((ConnHere _ _) (let-match erased (at-fn d t x x2 y2 px py) (Refl _ _)) (ConnHere h x2)))
  (let ((erased w2) (erased pw) (erased c2)) (adj-lift g h d t x w x2 a lf px))
  (conn-cat h x2 w2 y2 c2 (conn-lift g h d t w y w2 y2 c1 lf pw py)))

(def-fns _ $ (erased lift-zip : (erased (List (Bond)) g h) (erased (Nat) d t) (erased (List (Nat)) xs ys A B) (subterm erased (Zip xs ys g) z)
    (erased (Shf d t xs A) sa) (erased (Shf d t ys B) sb) (erased (Linked h A B) l) -> (erased (Lift h d t g) r))
  (let-match erased z (ZipCons xs1 ys1 g1 x y z1) ((ZipNil) (LiftNil h d t)))
  (let-match erased sa (ShfCons _ _ _ x2 _ As1 px sa1))
  (let-match erased sb (ShfCons _ _ _ y2 _ Bs1 py sb1))
  (let-match erased l (LinkCons _ _ _ _ _ c l1))
  (LiftCons h g1 d t x y x2 y2 px py c (lift-zip g1 h d t xs1 ys1 As1 Bs1 z1 sa1 sb1 l1)))

(def-fns _ $ (erased lift-cat : (erased (List (Bond)) g1 g2 g h) (erased (Nat) d t) (subterm erased (Cat g1 g2 g) c) (erased (Lift h d t g1) l1)
    (erased (Lift h d t g2) l2) -> (erased (Lift h d t g) r))
  (let-match erased c (CatCons g11 _ gg b c1) ((CatNil _) l2))
  (let-match erased l1 (LiftCons _ _ _ _ x y x2 y2 px py cn l11))
  (LiftCons h gg d t x y x2 y2 px py cn (lift-cat g11 g2 gg h d t c1 l11 l2)))

(def-fns _ $ (erased link-lift : (erased (List (Bond)) g h) (erased (Nat) d t) (erased (List (Nat)) xs ys A B) (subterm erased (Linked g xs ys) l)
    (erased (Lift h d t g) lf) (erased (Shf d t xs A) sa) (erased (Shf d t ys B) sb) -> (erased (Linked h A B) r))
  (let-match erased l (LinkCons _ xs1 ys1 x y c l1)
    ((LinkNil _) (let-match erased sa (ShfNil _ _)) (let-match erased sb (ShfNil _ _)) (LinkNil h)))
  (let-match erased sa (ShfCons _ _ _ x2 _ As1 px sa1))
  (let-match erased sb (ShfCons _ _ _ y2 _ Bs1 py sb1))
  (LinkCons h As1 Bs1 x2 y2 (conn-lift g h d t x y x2 y2 c lf px py) (link-lift g h d t xs1 ys1 As1 Bs1 l1 lf sa1 sb1)))

(def-fns _ $ (erased rooted-of : (erased (List (Bond)) g) (erased (List (Nat)) rs xs ls) (subterm erased (Linked g ls xs) l) (erased (Sub ls rs) sb)
    -> (erased (Rooted g rs xs ls) r))
  (let-match erased l (LinkCons _ ls1 xs1 r x c l1) ((LinkNil _) (RootedNil g rs)))
  (let-match erased sb (SubCons _ _ _ pin sb1))
  (RootedCons g rs xs1 ls1 x r pin c (rooted-of g rs xs1 ls1 l1 sb1)))

(def-fns _ $ (erased rooted-link : (erased (List (Bond)) g) (erased (List (Nat)) rs xs ls) (subterm erased (Rooted g rs xs ls) ro)
    -> (erased (Linked g ls xs) l) (erased (Sub ls rs) sb))
  (let-match erased ro (RootedCons _ _ xs1 ls1 x r pin c ro1) ((RootedNil _ _) (values (LinkNil g) (SubNil rs))))
  (let ((erased l1) (erased sb1)) (rooted-link g rs xs1 ls1 ro1))
  (values (LinkCons g ls1 xs1 r x c l1) (SubCons r ls1 rs pin sb1)))

(def-fns _ $ (erased shf-fn : (erased (Nat) d o) (erased (List (Nat)) p b b2) (subterm erased (Shf d o p b) s1) (erased (Shf d o p b2) s2)
    -> (erased (Eq (List (Nat)) b b2) e))
  (let-match erased s1 (ShfCons _ _ y z p1 c a1 s11) ((ShfNil _ _) (let-match erased s2 (ShfNil _ _)) (Refl _ b)))
  (let-match erased s2 (ShfCons _ _ _ z2 _ c2 a2 s21))
  (let-match erased (at-fn d o y z z2 a1 a2) (Refl _ _))
  (let-match erased (shf-fn d o p1 c c2 s11 s21) (Refl _ _))
  (Refl _ b))

; Block t of s is block t + t0 of ids.
(def-adts $ (Ident : ((Nat) t0) ((List (Nat)) ids) ((List (Blk)) s) -> Type)
  enum
  (many IdNil : (erased (Nat) t0) (erased (List (Nat)) ids) -> (Ident t0 ids (Nil (Blk))))
  (many IdCons : (erased (Nat) t0) (erased (List (Nat)) ids) (erased (List (Blk)) s) (erased (Ident (Succ t0) ids s) rest)
      -> (Ident t0 ids (Cons (Blk) (MkBlk t0 ids) s))))

(def-fns _ $ (erased ident-nth : (erased (Nat) t0 j o) (erased (List (Nat)) ids p) (erased (List (Blk)) s) (erased (Ident t0 ids s) id)
    (subterm erased (Nth (Blk) s j (MkBlk o p)) q) -> (erased (Add j t0 o) a) (erased (Eq (List (Nat)) p ids) e))
  (let-match erased id (IdCons _ _ s1 id1) (absurd (IdNil _ _) q))
  (let-match erased q (NthThere _ _ _ j1 _ q1) ((NthHere _ _ _) (values (AddZero t0) (Refl _ p))))
  (let ((erased a) (erased e)) (ident-nth (Succ t0) j1 o ids p s1 id1 q1))
  (values (add-succ-left j1 t0 o a) e))

; The identity laid out in blocks is the identity.
(def-fns _ $ (erased lay-iota : (erased (Nat) d m D) (erased (List (Nat)) ids L I) (erased (List (Blk)) s) (erased (Lay d s L) ly) (erased (Sized d s) sz)
    (erased (Ident (Zero) ids s) id) (erased (Iota d ids) io) (erased (Length (Blk) s m) ls) (erased (At d m (Zero) D) aD) (erased (Iota D I) ioD)
    -> (erased (Eq (List (Nat)) L I) e))
  (match erased (list-dec L I D (lay-length d m D s L ly sz ls aD) (iota-length D I ioD)) _
    ((OrL _ _ e) e)
    (absurd (OrR _ _ ne)
      (let-match erased ne (MkNeAt _ _ j a b pa pb ab))
      (let-match erased (iota-at D j b I ioD pb) (Refl _ _))
      (let ((erased t) (erased o) (erased p) (erased x) (erased y) (erased ps) (erased px) (erased az) (erased aw) (erased lx))
        (lay-nth-inv d j a s L ly sz pa))
      (let ((erased ad) (erased ep)) (ident-nth (Zero) t o ids p s id ps))
      (let-match erased ep (Refl _ _))
      (let-match erased (add-fn t (Zero) o t ad (add-zero-right t)) (Refl _ _))
      (let-match erased (iota-at d x y ids io px) (Refl _ _))
      (let-match erased (at-fn d t x j a az aw) (Refl _ _))
      (apart-irrefl j ab))))

; No block of s goes to block o.
(def-adts $ (Avoid : ((Nat) o) ((List (Blk)) s) -> Type)
  enum
  (many AvNil : (erased (Nat) o) -> (Avoid o (Nil (Blk))))
  (many AvCons : (erased (Nat) o o2) (erased (List (Nat)) p) (erased (List (Blk)) s) (erased (Apart (Nat) Lt o o2) ne) (erased (Avoid o s) rest)
      -> (Avoid o (Cons (Blk) (MkBlk o2 p) s))))

; The blocks of s go to distinct blocks, each to distinct darts.
(def-adts $ (Spread : ((Nat) d) ((List (Blk)) s) -> Type)
  enum
  (many SpreadNil : (erased (Nat) d) -> (Spread d (Nil (Blk))))
  (many SpreadCons : (erased (Nat) d o) (erased (List (Nat)) p) (erased (List (Blk)) s) (erased (Distinct p) dp) (erased (Under p d) up)
      (erased (Avoid o s) av) (erased (Spread d s) rest) -> (Spread d (Cons (Blk) (MkBlk o p) s))))

(def-fns _ $ (erased notin-join : (erased (Nat) z) (erased (List (Nat)) b r xs) (subterm erased (Join b r xs) j) (erased (NotIn z b) nb)
    (erased (NotIn z r) nr) -> (erased (NotIn z xs) res))
  (let-match erased j (JoinCons b1 _ xs1 x j1) ((JoinNil _) nr))
  (let-match erased nb (NotInCons _ _ _ ne nb1))
  (NotInCons z x xs1 ne (notin-join z b1 r xs1 j1 nb1 nr)))

(def-fns _ $ (erased shf-notin : (erased (Nat) d o o2 y z) (erased (List (Nat)) p b) (subterm erased (Shf d o2 p b) sh) (erased (Under p d) up)
    (erased (At d o y z) a) (erased (Lt y d) ly) (erased (Or (Apart (Nat) Lt o o2) (NotIn y p)) w) -> (erased (NotIn z b) r))
  (let-match erased sh (ShfCons _ _ y2 z2 p1 b1 a2 sh1) ((ShfNil _ _) (NotInNil z)))
  (let-match erased up (UnderCons _ _ _ l2 up1))
  (let-match erased w (OrR _ _ ni)
    ((OrL _ _ ne) (NotInCons z z2 b1 (at-apart d o y z o2 y2 z2 a a2 ly l2 (OrL _ _ ne)) (shf-notin d o o2 y z p1 b1 sh1 up1 a ly (OrL _ _ ne)))))
  (let-match erased ni (NotInCons _ _ _ ne ni1))
  (NotInCons z z2 b1 (at-apart d o y z o2 y2 z2 a a2 ly l2 (OrR _ _ ne)) (shf-notin d o o2 y z p1 b1 sh1 up1 a ly (OrR _ _ ni1))))

(def-fns _ $ (erased lay-avoid : (erased (Nat) d o y z) (erased (List (Blk)) s) (erased (List (Nat)) r) (subterm erased (Lay d s r) ly) (erased (Spread d s) sp)
    (erased (Avoid o s) av) (erased (At d o y z) a) (erased (Lt y d) l) -> (erased (NotIn z r) res))
  (let-match erased ly (LayCons _ o2 p b rest _ s1 sh j ly1) ((LayNil _) (NotInNil z)))
  (let-match erased sp (SpreadCons _ _ _ _ dp up _ sp1))
  (let-match erased av (AvCons _ _ _ _ ne av1))
  (notin-join z b rest r j (shf-notin d o o2 y z p b sh up a l (OrL _ _ ne)) (lay-avoid d o y z s1 rest ly1 sp1 av1 a l)))

(def-fns _ $ (erased distinct-shf : (erased (Nat) d o) (erased (List (Nat)) p b r xs) (erased (List (Blk)) s) (subterm erased (Shf d o p b) sh)
    (erased (Distinct p) dp) (erased (Under p d) up) (erased (Join b r xs) j) (erased (Distinct r) dr) (erased (Lay d s r) ly) (erased (Spread d s) sp)
    (erased (Avoid o s) av) -> (erased (Distinct xs) res))
  (let-match erased sh (ShfCons _ _ y z p1 b1 a sh1) ((ShfNil _ _) (let-match erased j (JoinNil _)) dr))
  (let-match erased j (JoinCons _ _ xs1 _ j1))
  (let-match erased dp (DistCons _ _ ny dp1))
  (let-match erased up (UnderCons _ _ _ l up1))
  (DistCons z xs1 (notin-join z b1 r xs1 j1 (shf-notin d o o y z p1 b1 sh1 up1 a l (OrR _ _ ny)) (lay-avoid d o y z s r ly sp av a l))
    (distinct-shf d o p1 b1 r xs1 s sh1 dp1 up1 j1 dr ly sp av)))

(def-fns _ $ (erased lay-distinct : (erased (Nat) d) (erased (List (Blk)) s) (erased (List (Nat)) xs) (subterm erased (Lay d s xs) ly) (erased (Spread d s) sp)
    -> (erased (Distinct xs) r))
  (let-match erased ly (LayCons _ o p b rest _ s1 sh j ly1) ((LayNil _) (DistNil)))
  (let-match erased sp (SpreadCons _ _ _ _ dp up av sp1))
  (distinct-shf d o p b rest xs s1 sh dp up j (lay-distinct d s1 rest ly1 sp1) ly1 sp1 av))

(def-fns _ $ (erased in-join-l : (erased (Nat) z) (erased (List (Nat)) b r xs) (subterm erased (Join b r xs) j) (erased (In z b) p) -> (erased (In z xs) res))
  (let-match erased j (JoinCons b1 _ xs1 x j1) (absurd (JoinNil _) p))
  (let-match erased p (InThere _ _ _ p1) ((InHere _ _) (InHere z xs1)))
  (InThere z x xs1 (in-join-l z b1 r xs1 j1 p1)))

(def-fns _ $ (erased in-join-r : (erased (Nat) z) (erased (List (Nat)) b r xs) (subterm erased (Join b r xs) j) (erased (In z r) p) -> (erased (In z xs) res))
  (let-match erased j (JoinCons b1 _ xs1 x j1) ((JoinNil _) p))
  (InThere z x xs1 (in-join-r z b1 r xs1 j1 p)))

(def-fns _ $ (erased shf-in : (erased (Nat) d o y z) (erased (List (Nat)) p b) (subterm erased (Shf d o p b) sh) (erased (In y p) pin) (erased (At d o y z) a)
    -> (erased (In z b) r))
  (let-match erased sh (ShfCons _ _ y2 z2 p1 b1 a2 sh1) (absurd (ShfNil _ _) pin))
  (let-match erased pin (InThere _ _ _ pin1)
    ((InHere _ _) (let-match erased (at-fn d o y z2 z a2 a) (Refl _ _)) (InHere z2 b1)))
  (InThere z z2 b1 (shf-in d o y z p1 b1 sh1 pin1 a)))

(def-fns _ $ (erased lay-in : (erased (Nat) d j a y z) (erased (List (Nat)) R rs) (erased (List (Blk)) s) (erased (Lay d s rs) ly)
    (subterm erased (Nth (Blk) s j (MkBlk a R)) pr) (erased (In y R) pin) (erased (At d a y z) az) -> (erased (In z rs) r))
  (let-match erased ly (LayCons _ o p b rest _ s1 sh jn ly1) (absurd (LayNil _) pr))
  (let-match erased pr (NthThere _ _ _ j1 _ pr1) ((NthHere _ _ _) (in-join-l z b rest rs jn (shf-in d a y z R b sh pin az))))
  (in-join-r z b rest rs jn (lay-in d j1 a y z R rest s1 ly1 pr1 pin az)))

; Each block (a, L) of sl has a block (a, R) in sr with every entry of L in R.
(def-adts $ (LSub : ((List (Blk)) sl sr) -> Type)
  enum
  (many LSNil : (erased (List (Blk)) sr) -> (LSub (Nil (Blk)) sr))
  (many LSCons : (erased (List (Blk)) sl sr) (erased (Nat) a j) (erased (List (Nat)) L R) (erased (Nth (Blk) sr j (MkBlk a R)) pr)
      (erased (Sub L R) sb) (erased (LSub sl sr) rest) -> (LSub (Cons (Blk) (MkBlk a L) sl) sr)))

(def-fns _ $ (erased shf-sub : (erased (Nat) d a j) (erased (List (Nat)) L R A rs) (erased (List (Blk)) sr) (subterm erased (Shf d a L A) sh)
    (erased (Sub L R) sb) (erased (Lay d sr rs) ly) (erased (Nth (Blk) sr j (MkBlk a R)) pr) -> (erased (Sub A rs) r))
  (let-match erased sh (ShfCons _ _ y z L1 As1 az sh1) ((ShfNil _ _) (SubNil rs)))
  (let-match erased sb (SubCons _ _ _ pin sb1))
  (SubCons z As1 rs (lay-in d j a y z R rs sr ly pr pin az) (shf-sub d a j L1 R As1 rs sr sh1 sb1 ly pr)))

(def-fns _ $ (erased sub-join : (erased (List (Nat)) A B C X) (subterm erased (Sub A X) sa) (erased (Sub B X) sb) (erased (Join A B C) j)
    -> (erased (Sub C X) r))
  (let-match erased sa (SubCons x As1 _ pin sa1) ((SubNil _) (let-match erased j (JoinNil _)) sb))
  (let-match erased j (JoinCons _ _ C1 _ j1))
  (SubCons x C1 X pin (sub-join As1 B C1 X sa1 sb j1)))

(def-fns _ $ (erased lay-sub : (erased (Nat) d) (erased (List (Blk)) sl sr) (erased (List (Nat)) lab rs) (subterm erased (Lay d sl lab) ll)
    (erased (Lay d sr rs) lr) (erased (LSub sl sr) ls) -> (erased (Sub lab rs) r))
  (let-match erased ll (LayCons _ a L A rest _ sl1 sh jn ll1) ((LayNil _) (SubNil rs)))
  (let-match erased ls (LSCons _ _ _ j _ R pr sb ls1))
  (sub-join A rest lab rs (shf-sub d a j L R A rs sr sh sb lr pr) (lay-sub d sl1 sr rest rs ll1 lr ls1) jn))

; Block by block, the darts that sa and sb lay out are linked in h.
(def-adts $ (LLink : ((Nat) d) ((List (Bond)) h) ((List (Blk)) sa sb) -> Type)
  enum
  (many LLNil : (erased (Nat) d) (erased (List (Bond)) h) -> (LLink d h (Nil (Blk)) (Nil (Blk))))
  (many LLCons : (erased (Nat) d a b) (erased (List (Bond)) h) (erased (List (Nat)) L M A B) (erased (List (Blk)) sa sb) (erased (Shf d a L A) shA)
      (erased (Shf d b M B) shB) (erased (Linked h A B) l) (erased (LLink d h sa sb) rest)
      -> (LLink d h (Cons (Blk) (MkBlk a L) sa) (Cons (Blk) (MkBlk b M) sb))))

(def-fns _ $ (erased lay-link : (erased (Nat) d) (erased (List (Bond)) h) (erased (List (Blk)) sa sb) (erased (List (Nat)) X Y) (subterm erased (Lay d sa X) lx)
    (erased (Lay d sb Y) ly) (erased (LLink d h sa sb) ll) -> (erased (Linked h X Y) r))
  (let-match erased ll (LLCons _ a b _ L M A2 Bs2 sa1 sb1 shA2 shB2 l ll1)
    ((LLNil _ _) (let-match erased lx (LayNil _)) (let-match erased ly (LayNil _)) (LinkNil h)))
  (let-match erased lx (LayCons _ _ _ A rx _ _ shA jx lx1))
  (let-match erased ly (LayCons _ _ _ B ry _ _ shB jy ly1))
  (let-match erased (shf-fn d a L A A2 shA shA2) (Refl _ _))
  (let-match erased (shf-fn d b M B Bs2 shB shB2) (Refl _ _))
  (link-join h A B rx ry X Y l (lay-link d h sa1 sb1 rx ry lx1 ly1 ll1) jx jy))

(def-adts $ (Laid : ((Nat) d) ((List (Blk)) s) ((List (Nat)) xs) -> Type)
  enum
  (many MkLaid : (erased (Nat) d) (erased (List (Blk)) s) (erased (List (Nat)) xs) (erased (Lay d s xs) ly) (erased (Sized d s) sz) -> (Laid d s xs)))

(def-fns _ $ (erased laid-exists : (erased (Nat) d) (erased (List (Blk)) s) (erased (Sized d s) sz) -> (erased (List (Nat)) xs) (erased (Laid d s xs) r))
  (let ((erased xs) (erased ly)) (lay-exists d s))
  (values xs (MkLaid d s xs ly sz)))

(def-fns _ $ (erased perm-parts : (erased (Nat) d) (erased (List (Nat)) p q ids) (erased (Perm d p q) pm) (erased (Iota d ids) io)
    -> (erased (Respects q p ids) qp) (erased (Respects p q ids) pq) (erased (Length (Nat) p d) lp) (erased (Length (Nat) q d) lq))
  (let-match erased pm (MkPerm _ _ _ ids1 io1 lp qp pq))
  (let-match erased (iota-fn d ids ids1 io io1) (Refl _ _))
  (values qp pq lp (respects-length-inv p q ids d pq (iota-length d ids io))))

; The cube of the hypermap (e, n, f) on d darts, on D = 6 d darts. Its blocks 0 to 5 are Gonthier's CTn, CTen, CTf,
; CTnf, CTe and CTfe; nf, ni and fi are the inverses of e, n and f, and I lists the D darts.
(def-adts $ (Cube : ((Nat) d D) ((List (Nat)) e n f ce cn cf) -> Type)
  enum
  (many MkCube : (erased (Nat) d D) (erased (List (Nat)) e n f ids nf ni fi ce cn cf cfi I)
      (erased (Iota d ids) io) (erased (Respects n f nf) rnf) (erased (Perm d e nf) pe) (erased (Perm d n ni) pn) (erased (Perm d f fi) pf)
      (erased (At d tg6 (Zero) D) aD) (erased (Iota D I) ioD)
      (erased (Laid d (Cons (Blk) (MkBlk tg5 ids) $ Cons (Blk) (MkBlk tg3 e) $ Cons (Blk) (MkBlk tg4 nf) $ Cons (Blk) (MkBlk tg1 nf) $
        Cons (Blk) (MkBlk tg2 e) $ Cons (Blk) (MkBlk (Zero) ids) $ Nil (Blk)) ce) le)
      (erased (Laid d (Cons (Blk) (MkBlk tg1 n) $ Cons (Blk) (MkBlk tg5 ids) $ Cons (Blk) (MkBlk tg3 e) $ Cons (Blk) (MkBlk tg4 nf) $
        Cons (Blk) (MkBlk tg2 ids) $ Cons (Blk) (MkBlk (Zero) ni) $ Nil (Blk)) cn) ln)
      (erased (Laid d (Cons (Blk) (MkBlk tg1 ids) $ Cons (Blk) (MkBlk tg2 ids) $ Cons (Blk) (MkBlk tg3 ids) $ Cons (Blk) (MkBlk (Zero) f) $
        Cons (Blk) (MkBlk tg4 e) $ Cons (Blk) (MkBlk tg5 n) $ Nil (Blk)) cf) lf)
      (erased (Laid d (Cons (Blk) (MkBlk tg3 fi) $ Cons (Blk) (MkBlk (Zero) ids) $ Cons (Blk) (MkBlk tg1 ids) $ Cons (Blk) (MkBlk tg2 ids) $
        Cons (Blk) (MkBlk tg4 nf) $ Cons (Blk) (MkBlk tg5 ni) $ Nil (Blk)) cfi) lfi)
      (erased (Laid d (Cons (Blk) (MkBlk (Zero) ids) $ Cons (Blk) (MkBlk tg1 ids) $ Cons (Blk) (MkBlk tg2 ids) $ Cons (Blk) (MkBlk tg3 ids) $
        Cons (Blk) (MkBlk tg4 ids) $ Cons (Blk) (MkBlk tg5 ids) $ Nil (Blk)) I) li)
      -> (Cube d D e n f ce cn cf)))

(def-fns _ $ (erased cube-exists : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h)
    -> (erased (Nat) D) (erased (List (Nat)) ce cn cf) (erased (Cube d D e n f ce cn cf) cu))
  (let ((erased nf) (erased ni) (erased fi) (erased rnf) (erased pe) (erased pn) (erased pf)) (hyper-core d e n f h))
  (let ((erased ids) (erased io)) (iota-exists d))
  (let ((erased _ec) (erased _ce) (erased lde) (erased ldnf)) (perm-parts d e nf ids pe io))
  (let ((erased _nc) (erased _cn) (erased ldn) (erased ldni)) (perm-parts d n ni ids pn io))
  (let ((erased _fc) (erased _cf) (erased ldf) (erased ldfi)) (perm-parts d f fi ids pf io))
  (let ((erased li)) (iota-length d ids io))
  (let ((erased D) (erased aD)) (at-exists d tg6 (Zero)))
  (let ((erased I) (erased ioD)) (iota-exists D))
  (let ((erased ce) (erased le)) (laid-exists d _ (SizedCons _ tg5 _ _ li $ SizedCons _ tg3 _ _ lde $ SizedCons _ tg4 _ _ ldnf $
    SizedCons _ tg1 _ _ ldnf $ SizedCons _ tg2 _ _ lde $ SizedCons _ (Zero) _ _ li $ SizedNil d)))
  (let ((erased cn) (erased ln)) (laid-exists d _ (SizedCons _ tg1 _ _ ldn $ SizedCons _ tg5 _ _ li $ SizedCons _ tg3 _ _ lde $
    SizedCons _ tg4 _ _ ldnf $ SizedCons _ tg2 _ _ li $ SizedCons _ (Zero) _ _ ldni $ SizedNil d)))
  (let ((erased cf) (erased lf)) (laid-exists d _ (SizedCons _ tg1 _ _ li $ SizedCons _ tg2 _ _ li $ SizedCons _ tg3 _ _ li $
    SizedCons _ (Zero) _ _ ldf $ SizedCons _ tg4 _ _ lde $ SizedCons _ tg5 _ _ ldn $ SizedNil d)))
  (let ((erased cfi) (erased lfi)) (laid-exists d _ (SizedCons _ tg3 _ _ ldfi $ SizedCons _ (Zero) _ _ li $ SizedCons _ tg1 _ _ li $
    SizedCons _ tg2 _ _ li $ SizedCons _ tg4 _ _ ldnf $ SizedCons _ tg5 _ _ ldni $ SizedNil d)))
  (let ((erased sid)) (Cons _ (MkBlk (Zero) ids) $ Cons _ (MkBlk tg1 ids) $ Cons _ (MkBlk tg2 ids) $ Cons _ (MkBlk tg3 ids) $
    Cons _ (MkBlk tg4 ids) $ Cons _ (MkBlk tg5 ids) $ Nil (Blk)))
  (let ((erased szid)) (SizedCons _ (Zero) _ _ li $ SizedCons _ tg1 _ _ li $ SizedCons _ tg2 _ _ li $ SizedCons _ tg3 _ _ li $ SizedCons _ tg4 _ _ li $
    SizedCons _ tg5 _ _ li $ SizedNil d))
  (let ((erased L) (erased lyL)) (lay-exists d sid))
  (let-match erased (lay-iota d tg6 D ids L I sid lyL szid
    (IdCons _ _ _ $ IdCons _ _ _ $ IdCons _ _ _ $ IdCons _ _ _ $ IdCons _ _ _ $ IdCons _ _ _ $ IdNil _ _) io
    (LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthNil _) aD ioD) (Refl _ _))
  (values D ce cn cf (MkCube d D e n f ids nf ni fi ce cn cf cfi I io rnf pe pn pf aD ioD le ln lf lfi (MkLaid d sid I lyL szid))))

; The length of a list of six blocks.
(def-fns _ $ (erased six : (erased (Blk) b0 b1 b2 b3 b4 b5) ->
    (erased (Length (Blk) (Cons (Blk) b0 $ Cons (Blk) b1 $ Cons (Blk) b2 $ Cons (Blk) b3 $ Cons (Blk) b4 $ Cons (Blk) b5 $ Nil (Blk)) tg6) l))
  (LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthNil _))

; The G-level composites the cube's blocks rest on.
(def-adts $ (Facts : ((Nat) d) ((List (Nat)) e n f ids nf ni fi) -> Type)
  enum
  (many MkFacts : (erased (Nat) d) (erased (List (Nat)) e n f ids nf ni fi)
      (erased (Respects ids ids ids) RI) (erased (Respects nf e ids) Rne) (erased (Respects e nf ids) Ren) (erased (Respects fi f ids) Rfif)
      (erased (Respects f fi ids) Rffi) (erased (Respects ni n ids) Rnin) (erased (Respects n ni ids) Rnni) (erased (Respects nf fi n) Rnffin)
      (erased (Respects e ids e) Reid) (erased (Respects nf ids nf) Rnfid) (erased (Respects ids ni ni) Ridni) (erased (Respects ids n n) Ridn)
      (erased (Respects ni ids ni) Rniid) (erased (Respects ids nf nf) Ridnf) (erased (Respects ids e e) Ride) (erased (Respects n ids n) Rnid)
      (erased (Respects f ids f) Rfid)
      (erased (Length (Nat) ids d) lid) (erased (Length (Nat) e d) le) (erased (Length (Nat) n d) ln) (erased (Length (Nat) f d) lf)
      (erased (Length (Nat) nf d) lnf) (erased (Length (Nat) ni d) lni) (erased (Length (Nat) fi d) lfi)
      (erased (Under e d) ue) (erased (Under n d) un) (erased (Under f d) uf) (erased (Under nf d) unf) (erased (Under ni d) uni)
      -> (Facts d e n f ids nf ni fi)))

(def-fns _ $ (erased facts : (erased (Nat) d) (erased (List (Nat)) e n f ids nf ni fi) (erased (Iota d ids) io) (erased (Respects n f nf) rnf)
    (erased (Perm d e nf) pe) (erased (Perm d n ni) pn) (erased (Perm d f fi) pf) -> (erased (Facts d e n f ids nf ni fi) r))
  (let ((erased Rne) (erased Ren) (erased le) (erased lnf)) (perm-parts d e nf ids pe io))
  (let ((erased Rnin) (erased Rnni) (erased ln) (erased lni)) (perm-parts d n ni ids pn io))
  (let ((erased Rfif) (erased Rffi) (erased lf) (erased lfi)) (perm-parts d f fi ids pf io))
  (let ((erased lid)) (iota-length d ids io))
  (let ((erased ue) (erased unf)) (values (perm-under d e nf pe) (perm-under d nf e (perm-sym d e nf pe))))
  (let ((erased un) (erased uni)) (values (perm-under d n ni pn) (perm-under d ni n (perm-sym d n ni pn))))
  (let ((erased Rnid)) (respects-id-right d ids n io ln))
  (MkFacts d e n f ids nf ni fi (respects-id-right d ids ids io lid) Rne Ren Rfif Rffi Rnin Rnni
    (respects-assoc fi f n ids nf n d Rffi Rnid rnf lnf lf)
    (respects-id-right d ids e io le) (respects-id-right d ids nf io lnf) (respects-id-left d ids ni io uni) (respects-id-left d ids n io un)
    (respects-id-right d ids ni io lni) (respects-id-left d ids nf io unf) (respects-id-left d ids e io ue) Rnid (respects-id-right d ids f io lf)
    lid le ln lf lnf lni lfi ue un (perm-under d f fi pf) unf uni))

; The cube is a hypermap: its edge permutation is an involution, its face permutation has the inverse cfi, and its node
; permutation is e . cfi.
(def-fns _ $ (erased cube-hyper : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu)
    -> (erased (Hypermap D ce cn cf) h))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased le (MkLaid _ _ _ lye sze))
  (let-match erased ln (MkLaid _ _ _ lyn szn))
  (let-match erased lf (MkLaid _ _ _ lyf szf))
  (let-match erased lfi (MkLaid _ _ _ lyfi szfi))
  (let-match erased li (MkLaid _ _ _ lyi szi))
  (let-match erased (facts d e n f ids nf ni fi io rnf pe pn pf)
    (MkFacts _ _ _ _ _ _ _ _ RI Rne Ren Rfif Rffi Rnin Rnni Rnffin Reid Rnfid Ridni _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  (let ((erased ee)) (lay-respects d _ _ _ ce ce I lye sze lye lyi
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ren $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) Ren $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RI $
      LRNil _)))
  (let ((erased fif)) (lay-respects d _ _ _ cfi cf I lyfi szfi lyf lyi
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) Rfif $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rnin $
      LRNil _)))
  (let ((erased ffi)) (lay-respects d _ _ _ cf cfi I lyf szf lyfi lyi
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rffi $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ren $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rnni $
      LRNil _)))
  (let ((erased efn)) (lay-respects d _ _ _ ce cfi cn lye sze lyfi lyn
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rnffin $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) Reid $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rnfid $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ren $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ridni $
      LRNil _)))
  (hyper-of D ce cf cfi cn (MkPerm D ce ce I ioD (lay-length d tg6 D _ ce lye sze (six _ _ _ _ _ _) aD) ee ee)
    (MkPerm D cf cfi I ioD (lay-length d tg6 D _ cf lyf szf (six _ _ _ _ _ _) aD) fif ffi) efn))

