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
      (erased (Under ids d) uid) (erased (Under fi d) ufi)
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
    lid le ln lf lnf lni lfi ue un (perm-under d f fi pf) unf uni (perm-under d ids ids (perm-id d ids io)) (perm-under d fi f (perm-sym d f fi pf))))

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
    (MkFacts _ _ _ _ _ _ _ _ RI Rne Ren Rfif Rffi Rnin Rnni Rnffin Reid Rnfid Ridni _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _))
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


(def-fns _ $ (erased respects-at : (erased (List (Nat)) lab xs ls) (erased (Nat) i j l) (subterm erased (Respects lab xs ls) rp)
    (erased (Nth (Nat) xs i j) p) (erased (Nth (Nat) lab j l) q) -> (erased (Nth (Nat) ls i l) r))
  (let-match erased rp (RespCons _ xs1 ls1 j1 l1 p1 rp1) (absurd (RespNil _) p))
  (let-match erased p (NthThere _ _ _ i1 _ p2)
    ((NthHere _ _ _) (let-match erased (nth-fn _ lab j l1 l p1 q) (Refl _ _)) (NthHere _ l1 ls1)))
  (NthThere _ l1 ls1 i1 l (respects-at lab xs1 ls1 i1 j l rp1 p2 q)))

; Block t of s goes to a block other than t + t0, and to darts of its block.
(def-adts $ (NoFix : ((Nat) d t0) ((List (Blk)) s) -> Type)
  enum
  (many NFNil : (erased (Nat) d t0) -> (NoFix d t0 (Nil (Blk))))
  (many NFCons : (erased (Nat) d t0 o) (erased (List (Nat)) p) (erased (List (Blk)) s) (erased (Apart (Nat) Lt o t0) ne) (erased (Under p d) up)
      (erased (NoFix d (Succ t0) s) rest) -> (NoFix d t0 (Cons (Blk) (MkBlk o p) s))))

(def-fns _ $ (erased nofix-nth : (erased (Nat) d t0 j o k) (erased (List (Nat)) p) (erased (List (Blk)) s) (erased (NoFix d t0 s) nf)
    (subterm erased (Nth (Blk) s j (MkBlk o p)) q) (erased (Add j t0 k) a) -> (erased (Apart (Nat) Lt o k) ne) (erased (Under p d) up))
  (let-match erased nf (NFCons _ _ _ _ s1 ne up nf1) (absurd (NFNil _ _) q))
  (let-match erased q (NthThere _ _ _ j1 _ q1)
    ((NthHere _ _ _) (let-match erased a (AddZero _)) (values ne up)))
  (let-match erased a (AddSucc _ _ k1 a1))
  (nofix-nth d (Succ t0) j1 o k p s1 nf1 q1 (add-succ-right j1 t0 k1 a1)))

; A list laid out without fixed blocks moves every dart.
(def-fns _ $ (erased lay-apart : (erased (Nat) d z w) (erased (List (Blk)) s) (erased (List (Nat)) xs) (erased (Lay d s xs) ly) (erased (Sized d s) sz)
    (erased (NoFix d (Zero) s) nf) (erased (Nth (Nat) xs z w) pz) -> (erased (Apart (Nat) Lt w z) r))
  (let ((erased t) (erased o) (erased p) (erased x) (erased y) (erased ps) (erased px) (erased az) (erased aw) (erased lx))
    (lay-nth-inv d z w s xs ly sz pz))
  (let ((erased ne) (erased up)) (nofix-nth d (Zero) t o t p s nf ps (add-zero-right t)))
  (at-apart d o y w t x z aw az (under-nth p x y d up px) lx (OrL _ _ ne)))

(def-fns _ $ (erased order-of-two : (erased (List (Nat)) p) (erased (Nat) z w) (erased (Nth (Nat) p z w) pz) (erased (Nth (Nat) p w z) pw)
    (erased (Apart (Nat) Lt w z) ne) -> (erased (Order p z tg2) r))
  (MkOrder p (Cons _ w (Nil _)) z w (Succ (Zero)) pz
    (PathStep p (Cons _ z (Nil _)) (Nil _) w z z pw (NotInCons w z (Nil _) ne (NotInNil w)) (PathHere p (Cons _ z (Nil _)) z))
    (LengthCons _ w (Nil _) (Zero) (LengthNil _))))

(def-fns _ $ (erased order-of-three : (erased (List (Nat)) p) (erased (Nat) z w u) (erased (Nth (Nat) p z w) pz) (erased (Nth (Nat) p w u) pw)
    (erased (Nth (Nat) p u z) pu) (erased (Apart (Nat) Lt w z) nw) (erased (Apart (Nat) Lt u z) nu) -> (erased (Order p z tg3) r))
  (let ((erased zs)) (Cons _ z (Nil _)))
  (MkOrder p (Cons _ w (Cons _ u (Nil _))) z w tg2 pz
    (PathStep p zs (Cons _ u (Nil _)) w u z pw (NotInCons w z (Nil _) nw (NotInNil w))
      (PathStep p zs (Nil _) u z z pu (NotInCons u z (Nil _) nu (NotInNil u)) (PathHere p zs z)))
    (LengthCons _ w _ _ (LengthCons _ u (Nil _) (Zero) (LengthNil _)))))

; Every dart of an involution laid out without fixed blocks has order 2.
(def-fns _ $ (erased orders-two : (erased (Nat) d D n) (erased (List (Nat)) p q I xs) (erased (List (Blk)) s) (erased (Lay d s p) ly) (erased (Sized d s) sz)
    (erased (NoFix d (Zero) s) nf) (erased (Perm D p q) pm) (erased (Respects p p I) pp) (erased (Iota D I) io)
    (subterm erased (Length (Nat) xs n) lx) (erased (Under xs D) ux) -> (erased (List (Nat)) ks) (erased (Orders p xs ks) os) (erased (Repeat (Nat) n tg2 ks) rk))
  (let-match erased lx (LengthCons _ z xs1 n1 lx1) ((LengthNil _) (values (Nil _) (OrdNil p) (RepeatNil _ tg2))))
  (let-match erased ux (UnderCons _ _ _ lz ux1))
  (let ((erased w) (erased pz) (erased lw)) (perm-nth D z p q pm lz))
  (let ((erased pw)) (respects-nth p p I z w z pp pz (iota-nth D z I io lz)))
  (let ((erased ks) (erased os) (erased rk)) (orders-two d D n1 p q I xs1 s ly sz nf pm pp io lx1 ux1))
  (values (Cons _ tg2 ks) (OrdCons p xs1 ks z tg2 (order-of-two p z w pz pw (lay-apart d z w s p ly sz nf pz)) os) (RepeatCons _ n1 tg2 ks rk)))

; Every dart of a permutation p laid out without fixed blocks, with p . p = p2 and p . p2 the identity, and p2 laid out
; without fixed blocks, has order 3.
(def-fns _ $ (erased orders-three : (erased (Nat) d D n) (erased (List (Nat)) p q p2 I xs) (erased (List (Blk)) s s2) (erased (Lay d s p) ly)
    (erased (Sized d s) sz) (erased (NoFix d (Zero) s) nf) (erased (Lay d s2 p2) ly2) (erased (Sized d s2) sz2) (erased (NoFix d (Zero) s2) nf2)
    (erased (Perm D p q) pm) (erased (Respects p p p2) r2) (erased (Respects p p2 I) r3) (erased (Iota D I) io)
    (subterm erased (Length (Nat) xs n) lx) (erased (Under xs D) ux) -> (erased (List (Nat)) ks) (erased (Orders p xs ks) os) (erased (Repeat (Nat) n tg3 ks) rk))
  (let-match erased lx (LengthCons _ z xs1 n1 lx1) ((LengthNil _) (values (Nil _) (OrdNil p) (RepeatNil _ tg3))))
  (let-match erased ux (UnderCons _ _ _ lz ux1))
  (let ((erased w) (erased pz) (erased lw)) (perm-nth D z p q pm lz))
  (let ((erased u) (erased pw) (erased lu)) (perm-nth D w p q pm lw))
  (let ((erased p2z)) (respects-at p p p2 z w u r2 pz pw))
  (let ((erased pu)) (respects-nth p p2 I z u z r3 p2z (iota-nth D z I io lz)))
  (let ((erased ks) (erased os) (erased rk)) (orders-three d D n1 p q p2 I xs1 s s2 ly sz nf ly2 sz2 nf2 pm r2 r3 io lx1 ux1))
  (values (Cons _ tg3 ks)
    (OrdCons p xs1 ks z tg3 (order-of-three p z w u pz pw pu (lay-apart d z w s p ly sz nf pz) (lay-apart d z u s2 p2 ly2 sz2 nf2 p2z)) os)
    (RepeatCons _ n1 tg3 ks rk)))

; The cube is plain.
(def-fns _ $ (erased cube-plain : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu)
    -> (erased (AllOrder D ce tg2) r))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased le (MkLaid _ _ _ lye sze))
  (let-match erased li (MkLaid _ _ _ lyi szi))
  (let-match erased (facts d e n f ids nf ni fi io rnf pe pn pf)
    (MkFacts _ _ _ _ _ _ _ _ RI Rne Ren _ _ _ _ _ _ _ _ _ _ _ _ _ _ lid _ _ _ _ _ _ ue un _ unf uni uid _))
  (let ((erased ee)) (lay-respects d _ _ _ ce ce I lye sze lye lyi
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ren $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) Ren $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RI $
      LRNil _)))
  (let ((erased lD)) (iota-length D I ioD))
  (let ((erased ks) (erased os) (erased rk)) (orders-two d D D ce ce I I _ lye sze
    (NFCons _ _ _ _ _ (ApGt _ _ _ _ (LtZ _)) uid $
      NFCons _ _ _ _ _ (ApGt _ _ _ _ (LtS _ _ (LtZ _))) ue $
      NFCons _ _ _ _ _ (ApGt _ _ _ _ (LtS _ _ (LtS _ _ (LtZ _)))) unf $
      NFCons _ _ _ _ _ (ApLt _ _ _ _ (LtS _ _ (LtZ _))) unf $
      NFCons _ _ _ _ _ (ApLt _ _ _ _ (LtS _ _ (LtS _ _ (LtZ _)))) ue $
      NFCons _ _ _ _ _ (ApLt _ _ _ _ (LtZ _)) uid $
      NFNil _ _)
    (MkPerm D ce ce I ioD (lay-length d tg6 D _ ce lye sze (six _ _ _ _ _ _) aD) ee ee) ee ioD lD (perm-under D I I (perm-id D I ioD))))
  (MkAllOrder D tg2 ce ks (MkOrderList D ce I ks ioD os) rk))

; The cube is cubic.
(def-fns _ $ (erased cube-cubic : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu)
    -> (erased (AllOrder D cn tg3) r))
  (let ((erased q) (erased pm)) (hyper-perm D cn cf ce (hyper-rot D ce cn cf (cube-hyper d D e n f ce cn cf cu))))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased ln (MkLaid _ _ _ lyn szn))
  (let-match erased li (MkLaid _ _ _ lyi szi))
  (let-match erased (facts d e n f ids nf ni fi io rnf pe pn pf)
    (MkFacts _ _ _ _ _ _ _ _ RI Rne Ren _ _ Rnin Rnni _ Reid _ _ Ridn Rniid Ridnf _ _ _ lid lde ldn _ lnf lni _ ue un _ unf uni uid _))
  (let ((erased s2)) (Cons _ (MkBlk tg5 n) $ Cons _ (MkBlk (Zero) ni) $ Cons _ (MkBlk tg4 ids) $ Cons _ (MkBlk tg2 nf) $ Cons _ (MkBlk tg3 e) $
    Cons _ (MkBlk tg1 ids) $ Nil (Blk)))
  (let ((erased sz2)) (SizedCons _ tg5 _ _ ldn $ SizedCons _ (Zero) _ _ lni $ SizedCons _ tg4 _ _ lid $ SizedCons _ tg2 _ _ lnf $ SizedCons _ tg3 _ _ lde $ SizedCons _ tg1 _ _ lid $ SizedNil d))
  (let ((erased cn2) (erased ly2)) (lay-exists d s2))
  (let ((erased r2)) (lay-respects d _ _ _ cn cn cn2 lyn szn lyn ly2
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) Ridn $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rniid $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ridnf $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Reid $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) Rnni $
      LRNil _)))
  (let ((erased r3)) (lay-respects d _ _ _ cn cn2 I lyn szn ly2 lyi
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rnin $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) Rnni $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ren $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRNil _)))
  (let ((erased ks) (erased os) (erased rk)) (orders-three d D D cn q cn2 I I _ _ lyn szn
    (NFCons _ _ _ _ _ (ApGt _ _ _ _ (LtZ _)) un $
      NFCons _ _ _ _ _ (ApGt _ _ _ _ (LtS _ _ (LtZ _))) uid $
      NFCons _ _ _ _ _ (ApGt _ _ _ _ (LtS _ _ (LtS _ _ (LtZ _)))) ue $
      NFCons _ _ _ _ _ (ApGt _ _ _ _ (LtS _ _ (LtS _ _ (LtS _ _ (LtZ _))))) unf $
      NFCons _ _ _ _ _ (ApLt _ _ _ _ (LtS _ _ (LtS _ _ (LtZ _)))) uid $
      NFCons _ _ _ _ _ (ApLt _ _ _ _ (LtZ _)) uni $
      NFNil _ _)
    ly2 sz2
    (NFCons _ _ _ _ _ (ApGt _ _ _ _ (LtZ _)) un $
      NFCons _ _ _ _ _ (ApLt _ _ _ _ (LtZ _)) uni $
      NFCons _ _ _ _ _ (ApGt _ _ _ _ (LtS _ _ (LtS _ _ (LtZ _)))) uid $
      NFCons _ _ _ _ _ (ApLt _ _ _ _ (LtS _ _ (LtS _ _ (LtZ _)))) unf $
      NFCons _ _ _ _ _ (ApLt _ _ _ _ (LtS _ _ (LtS _ _ (LtS _ _ (LtZ _))))) ue $
      NFCons _ _ _ _ _ (ApLt _ _ _ _ (LtS _ _ (LtZ _))) uid $
      NFNil _ _)
    pm r2 r3 ioD (iota-length D I ioD) (perm-under D I I (perm-id D I ioD))))
  (MkAllOrder D tg3 cn ks (MkOrderList D cn I ks ioD os) rk))


(def-fns _ $ (erased under-notin : (erased (List (Nat)) xs) (erased (Nat) n) (subterm erased (Under xs n) u) -> (erased (NotIn n xs) r))
  (let-match erased u (UnderCons xs1 x _ l u1) ((UnderNil _) (NotInNil n)))
  (NotInCons n x xs1 (ApGt _ _ n x l) (under-notin xs1 n u1)))

(def-fns _ $ (erased iota-distinct : (erased (Nat) d) (erased (List (Nat)) ids) (subterm erased (Iota d ids) io) -> (erased (Distinct ids) r))
  (let-match erased io (IotaS n ids1 _ io1 sn) ((IotaZ) (DistNil)))
  (distinct-snoc-cons n ids1 ids sn
    (DistCons n ids1 (under-notin ids1 n (perm-under n ids1 ids1 (perm-id n ids1 io1))) (iota-distinct n ids1 io1))))

(def-fns _ $ (erased under-sub : (erased (Nat) d) (erased (List (Nat)) xs ids) (subterm erased (Under xs d) u) (erased (Iota d ids) io)
    -> (erased (Sub xs ids) r))
  (let-match erased u (UnderCons xs1 x _ l u1) ((UnderNil _) (SubNil ids)))
  (SubCons x xs1 ids (iota-in d x ids io l) (under-sub d xs1 ids u1 io)))

; A labelling constant along the graph of p is constant along p.
(def-fns _ $ (erased graph-resp : (erased (Nat) d) (erased (List (Nat)) p lab) (erased (List (Bond)) g) (erased (Graph d p g) gr)
    (erased (Const lab g) cl) (erased (Length (Nat) lab d) ll) -> (erased (Respects lab p lab) r))
  (let-match erased gr (MkGraph _ _ ids _ io lp z))
  (const-respects lab ids p lab g z cl (respects-id-right d ids lab io ll)))

; Each block of s has k_i darts, and k is their sum.
(def-adts $ (BLens : ((List (Blk)) s) ((Nat) k) -> Type)
  enum
  (many BLenNil : -> (BLens (Nil (Blk)) (Zero)))
  (many BLenCons : (erased (List (Blk)) s) (erased (Nat) o k1 k2 k) (erased (List (Nat)) p) (erased (Length (Nat) p k1) lp) (erased (BLens s k2) rest)
      (erased (Add k1 k2 k) a) -> (BLens (Cons (Blk) (MkBlk o p) s) k)))

(def-fns _ $ (erased lay-len : (erased (Nat) d k) (erased (List (Blk)) s) (erased (List (Nat)) xs) (subterm erased (Lay d s xs) ly) (erased (BLens s k) bl)
    -> (erased (Length (Nat) xs k) r))
  (let-match erased ly (LayCons _ o p b rest _ s1 sh j ly1) ((LayNil _) (let-match erased bl (BLenNil)) (LengthNil _)))
  (let-match erased bl (BLenCons _ _ k1 k2 _ _ lp bl1 a))
  (join-length b rest xs k1 k2 k j (shf-length d o k1 p b sh lp) (lay-len d k2 s1 rest ly1 bl1) a))

; A count of classes from a laid-out labelling lab and laid-out roots rs.
(def-fns _ $ (erased lay-classes : (erased (Nat) d D m k) (erased (List (Blk)) sl sr sid) (erased (List (Nat)) lab rs I) (erased (List (Bond)) g)
    (erased (Laid d sl lab) ll) (erased (Length (Blk) sl m) lsl) (erased (At d m (Zero) D) aD) (erased (Lay d sr rs) lr) (erased (Spread d sr) sp)
    (erased (BLens sr k) bl) (erased (Laid d sid I) li) (erased (Iota D I) io) (erased (LResp sl sr sr) fix) (erased (Const lab g) cl)
    (erased (LSub sl sr) ls) (erased (LLink d g sl sid) lk) -> (erased (Classes g D k) r))
  (let-match erased ll (MkLaid _ _ _ lyl szl))
  (let-match erased li (MkLaid _ _ _ lyi szi))
  (MkClasses g D k I lab rs io (lay-length d m D sl lab lyl szl lsl aD) (lay-len d k sr rs lr bl) (lay-distinct d sr rs lr sp)
    (lay-respects d sl sr sr lab rs rs lyl szl lr lr fix) cl
    (rooted-of g rs I lab (lay-link d g sl sid lab I lyl lyi lk) (lay-sub d sl sr lab rs lyl lr ls))))

; One step along the laid-out permutation p links block a of P to block b of Q.
(def-fns _ $ (erased blk-step : (erased (Nat) d D a b) (erased (List (Blk)) sp) (erased (List (Nat)) p R P Q A B) (erased (List (Bond)) g)
    (erased (Laid d sp p) lp) (erased (Graph D p g) gr) (erased (Nth (Blk) sp a (MkBlk b R)) pa) (erased (Respects R P Q) rp)
    (erased (Shf d a P A) sa) (erased (Shf d b Q B) sb) -> (erased (Linked g A B) r))
  (let-match erased lp (MkLaid _ _ _ ly sz))
  (link-step D p A B g gr (shf-respects d a b sp p R P Q A B ly sz pa rp sa sb)))

(def-fns _ $ (erased sep-apart : (erased (Nat) d x y l1 l2) (erased (List (Nat)) ids lab rs) (erased (List (Bond)) h) (erased (Sep h x y) s)
    (erased (Iota d ids) io) (erased (Rooted h rs ids lab) ro) (erased (Nth (Nat) lab x l1) p1) (erased (Nth (Nat) lab y l2) p2)
    (erased (Lt x d) lx) (erased (Lt y d) ly) -> (erased (Apart (Nat) Lt l1 l2) r))
  (let-match erased (nat-eq l1 l2) (Unequal _ _ _ _ ne)
    (absurd (Equal _ _ _)
      (let ((erased _i1) (erased c1)) (classes-root h d ids lab rs x l1 io ro p1 lx))
      (let ((erased _i2) (erased c2)) (classes-root h d ids lab rs y l1 io ro p2 ly))
      (sep-conn h x y s (conn-cat h x l1 y (conn-sym h l1 x c1) c2))))
  ne)

; The labels of the two ends of each bond of g, told apart in h, differ.
(def-fns _ $ (erased allsep-differ : (erased (Nat) d) (erased (List (Nat)) X Y LX LY ids lab rs) (erased (List (Bond)) g h) (subterm erased (Zip X Y g) z)
    (erased (AllSep h g) sp) (erased (Respects lab X LX) rx) (erased (Respects lab Y LY) ry) (erased (Under X d) ux) (erased (Under Y d) uy)
    (erased (Iota d ids) io) (erased (Rooted h rs ids lab) ro) -> (erased (Differ LX LY) r))
  (let-match erased z (ZipCons X1 Y1 g1 x y z1) ((ZipNil) (let-match erased rx (RespNil _)) (let-match erased ry (RespNil _)) (DifferNil)))
  (let-match erased sp (AllSepCons _ _ _ _ s sp1))
  (let-match erased rx (RespCons _ _ LX1 _ l1 p1 rx1))
  (let-match erased ry (RespCons _ _ LY1 _ l2 p2 ry1))
  (let-match erased ux (UnderCons _ _ _ lx ux1))
  (let-match erased uy (UnderCons _ _ _ ly uy1))
  (DifferCons LX1 LY1 l1 l2 (sep-apart d x y l1 l2 ids lab rs h s io ro p1 p2 lx ly)
    (allsep-differ d X1 Y1 LX1 LY1 ids lab rs g1 h z1 sp1 rx1 ry1 ux1 uy1 io ro)))

; Each bond of the inverse q of p is told apart if each bond of p is.
(def-fns _ $ (erased allsep-inv : (erased (Nat) d) (erased (List (Nat)) p q) (erased (List (Bond)) gp gq h) (subterm erased (Fun q gq) fq)
    (erased (Perm d q p) pm) (erased (Graph d p gp) gr) (erased (AllSep h gp) sp) -> (erased (AllSep h gq) r))
  (let-match erased fq (FunCons _ g1 x y py f1) ((FunNil _) (AllSepNil h)))
  (AllSepCons h g1 x y (sep-sym h y x (allsep-adj h gp y x (graph-adj d y x p gp gr (perm-inv d x y q p pm py)) sp))
    (allsep-inv d p q gp g1 h f1 pm gr sp)))

; Bonds whose ends have different labels under a labelling constant along h are told apart in h.
(def-fns _ $ (erased allsep-of : (erased (List (Nat)) X Y LX LY lab) (erased (List (Bond)) g h) (subterm erased (Zip X Y g) z)
    (erased (Respects lab X LX) rx) (erased (Respects lab Y LY) ry) (erased (Differ LX LY) df) (erased (Const lab h) cl) -> (erased (AllSep h g) r))
  (let-match erased z (ZipCons X1 Y1 g1 x y z1) ((ZipNil) (AllSepNil h)))
  (let-match erased rx (RespCons _ _ LX1 _ l1 p1 rx1))
  (let-match erased ry (RespCons _ _ LY1 _ l2 p2 ry1))
  (let-match erased df (DifferCons _ _ _ _ ne df1))
  (AllSepCons h g1 x y (MkSep h x y lab l1 l2 cl p1 p2 ne) (allsep-of X1 Y1 LX1 LY1 lab g1 h z1 rx1 ry1 df1 cl)))

(def-fns _ $ (erased differ-shf : (erased (Nat) d a b k) (erased (List (Nat)) P Q X Y) (subterm erased (Shf d a P X) sx) (erased (Shf d b Q Y) sy)
    (erased (Length (Nat) P k) lp) (erased (Length (Nat) Q k) lq) (erased (Under P d) up) (erased (Under Q d) uq)
    (erased (Or (Apart (Nat) Lt a b) (Differ P Q)) o) -> (erased (Differ X Y) r))
  (let-match erased sx (ShfCons _ _ x u P1 X1 ax sx1)
    ((ShfNil _ _) (let-match erased lp (LengthNil _)) (let-match erased lq (LengthNil _)) (let-match erased sy (ShfNil _ _)) (DifferNil)))
  (let-match erased sy (ShfCons _ _ y v Q1 Y1 ay sy1) (absurd (ShfNil _ _) (let-match erased lp (LengthCons _ _ _ _ _)) lq))
  (let-match erased lp (LengthCons _ _ _ k1 lp1))
  (let-match erased lq (LengthCons _ _ _ _ lq1))
  (let-match erased up (UnderCons _ _ _ lx up1))
  (let-match erased uq (UnderCons _ _ _ ly uq1))
  (let-match erased o (OrR _ _ df)
    ((OrL _ _ ne) (DifferCons X1 Y1 u v (at-apart d a x u b y v ax ay lx ly (OrL _ _ ne)) (differ-shf d a b k1 P1 Q1 X1 Y1 sx1 sy1 lp1 lq1 up1 uq1 (OrL _ _ ne)))))
  (let-match erased df (DifferCons _ _ _ _ ne df1))
  (DifferCons X1 Y1 u v (at-apart d a x u b y v ax ay lx ly (OrR _ _ ne)) (differ-shf d a b k1 P1 Q1 X1 Y1 sx1 sy1 lp1 lq1 up1 uq1 (OrR _ _ df1))))

(def-fns _ $ (erased differ-join : (erased (List (Nat)) A B r rb xs ys) (subterm erased (Differ A B) p) (erased (Differ r rb) q)
    (erased (Join A r xs) j1) (erased (Join B rb ys) j2) -> (erased (Differ xs ys) res))
  (let-match erased p (DifferCons As1 Bs1 x y ne p1)
    ((DifferNil) (let-match erased j1 (JoinNil _)) (let-match erased j2 (JoinNil _)) q))
  (let-match erased j1 (JoinCons _ _ xs1 _ j11))
  (let-match erased j2 (JoinCons _ _ ys1 _ j21))
  (DifferCons xs1 ys1 x y ne (differ-join As1 Bs1 r rb xs1 ys1 p1 q j11 j21)))

; Block by block, the darts that sa and sb lay out are in different blocks or at different positions.
(def-adts $ (LDiffer : ((Nat) d) ((List (Blk)) sa sb) -> Type)
  enum
  (many LDNil : (erased (Nat) d) -> (LDiffer d (Nil (Blk)) (Nil (Blk))))
  (many LDCons : (erased (Nat) d a b) (erased (List (Nat)) P Q) (erased (List (Blk)) sa sb) (erased (Length (Nat) P d) lp) (erased (Length (Nat) Q d) lq)
      (erased (Under P d) up) (erased (Under Q d) uq) (erased (Or (Apart (Nat) Lt a b) (Differ P Q)) o) (erased (LDiffer d sa sb) rest)
      -> (LDiffer d (Cons (Blk) (MkBlk a P) sa) (Cons (Blk) (MkBlk b Q) sb))))

(def-fns _ $ (erased lay-differ : (erased (Nat) d) (erased (List (Blk)) sa sb) (erased (List (Nat)) X Y) (erased (Lay d sa X) lx) (erased (Lay d sb Y) ly)
    (subterm erased (LDiffer d sa sb) ld) -> (erased (Differ X Y) r))
  (let-match erased ld (LDCons _ a b P Q sa1 sb1 lp lq up uq o ld1)
    ((LDNil _) (let-match erased lx (LayNil _)) (let-match erased ly (LayNil _)) (DifferNil)))
  (let-match erased lx (LayCons _ _ _ A rx _ _ sA jx lx1))
  (let-match erased ly (LayCons _ _ _ B ry _ _ sB jy ly1))
  (differ-join A B rx ry X Y (differ-shf d a b d P Q A B sA sB lp lq up uq o) (lay-differ d sa1 sb1 rx ry lx1 ly1 ld1) jx jy))

(def-fns _ $ (erased differ-nth : (erased (List (Nat)) X Y) (erased (Nat) a u v) (subterm erased (Differ X Y) df) (erased (Nth (Nat) X a u) pu)
    (erased (Nth (Nat) Y a v) pv) -> (erased (Apart (Nat) Lt u v) r))
  (let-match erased df (DifferCons X1 Y1 x y ne df1) (absurd (DifferNil) pu))
  (let-match erased pu (NthThere _ _ _ a1 _ pu1) ((NthHere _ _ _) (let-match erased pv (NthHere _ _ _)) ne))
  (let-match erased pv (NthThere _ _ _ _ _ pv1))
  (differ-nth X1 Y1 a1 u v df1 pu1 pv1))

(def-fns _ $ (erased differ-restrict : (erased (List (Nat)) X Y A XA YA) (erased (Differ X Y) df) (subterm erased (Respects X A XA) rx)
    (erased (Respects Y A YA) ry) -> (erased (Differ XA YA) r))
  (let-match erased rx (RespCons _ As1 XAs1 a u pu rx1) ((RespNil _) (let-match erased ry (RespNil _)) (DifferNil)))
  (let-match erased ry (RespCons _ _ YAs1 _ v pv ry1))
  (DifferCons XAs1 YAs1 u v (differ-nth X Y a u v df pu pv) (differ-restrict X Y As1 XAs1 YAs1 df rx1 ry1)))

; K is constant along p, so K . (p . A) = K . A.
(def-fns _ $ (erased const-step : (erased (List (Nat)) K p A B Y) (erased (Respects K p K) kp) (subterm erased (Respects p A B) rp)
    (erased (Respects K A Y) ry) -> (erased (Respects K B Y) r))
  (let-match erased rp (RespCons _ As1 Bs1 a b pab rp1) ((RespNil _) (let-match erased ry (RespNil _)) (RespNil K)))
  (let-match erased ry (RespCons _ _ Y1 _ k pk ry1))
  (RespCons K Bs1 Y1 b k (respects-nth K p K a b k kp pab pk) (const-step K p As1 Bs1 Y1 kp rp1 ry1)))

; Block o of ids, then P, is block o of P.
(def-fns _ $ (erased shf-compose : (erased (Nat) d o) (erased (List (Nat)) ids P B C) (erased (Iota d ids) io) (erased (Shf d o ids B) sb)
    (subterm erased (Shf d o P C) sc) (erased (Under P d) up) -> (erased (Respects B P C) r))
  (let-match erased sc (ShfCons _ _ y z P1 C1 a sc1) ((ShfNil _ _) (RespNil B)))
  (let-match erased up (UnderCons _ _ _ ly up1))
  (RespCons B P1 C1 y z (shf-nth d o y y z ids B sb (iota-nth d y ids io ly) a) (shf-compose d o ids P1 B C1 io sb sc1 up1)))

(def-fns _ $ (erased at-add : (erased (Nat) d t u v A B) (subterm erased (At d t (Zero) A) pa) (erased (At d u (Zero) B) pb) (erased (Add t u v) a)
    -> (erased (Nat) C) (erased (Add A B C) ac) (erased (At d v (Zero) C) pc))
  (let-match erased pa (AtS _ t1 _ As1 _ pa1 ad) ((AtZ _ _) (let-match erased a (AddZero _)) (values B (AddZero B) pb)))
  (let-match erased a (AddSucc _ _ v1 a1))
  (let ((erased C1) (erased ac1) (erased pc1)) (at-add d t1 u v1 As1 B pa1 pb a1))
  (let ((erased C) (erased dc)) (add d C1))
  (let ((erased ab) (erased dab) (erased abc)) (add-assoc-inv d As1 B C1 C ac1 dc))
  (let-match erased (add-fn d As1 ab A dab ad) (Refl _ _))
  (values C abc (AtS d v1 (Zero) C1 C pc1 dc)))

; The Euler sum of the cube, from that of the map: 2 kc + 6 d = 3 d + 2 d + (ke + (kn + kf)) + 2 gen.
(def-fns _ $ (erased es-cube : (erased (Nat) kc d ke kn kf gen D K3 K2 a kF) (erased (EulerSum kc d ke kn kf gen) es) (erased (At d tg6 (Zero) D) aD)
    (erased (At d tg3 (Zero) K3) a3) (erased (At d tg2 (Zero) K2) a2) (erased (Add kn kf a) a1) (erased (Add ke a kF) a0)
    -> (erased (EulerSum kc D K3 K2 kF gen) r))
  (let-match erased es (MkEulerSum _ _ _ _ _ _ c2 lhs s1 rhs g2 dc al as1 ar dg ag))
  (let ((erased K5) (erased a35) (erased a5)) (at-add d tg3 tg2 tg5 K3 K2 a3 a2 (AddSucc _ _ _ $ AddSucc _ _ _ $ AddSucc _ _ _ $ AddZero _)))
  (let-match erased aD (AtS _ _ _ D5 _ aD5 dD))
  (let-match erased (at-fn d tg5 (Zero) D5 K5 aD5 a5) (Refl _ _))
  (let ((erased s0) (erased p0) (erased q0)) (add-assoc-inv ke kn kf a kF a1 a0))
  (let-match erased (add-fn ke kn s0 s1 p0 as1) (Refl _ _))
  (let-match erased (add-fn s1 kf kF rhs q0 ar) (Refl _ _))
  (let ((erased lhs2) (erased al2)) (add c2 D))
  (let ((erased ab) (erased p1) (erased q1)) (add-assoc-inv c2 d K5 D lhs2 dD al2))
  (let-match erased (add-fn c2 d ab lhs p1 al) (Refl _ _))
  (let ((erased rhs2) (erased ar2)) (add K5 rhs))
  (let ((erased bc) (erased p2) (erased q2)) (add-assoc g2 rhs K5 lhs lhs2 ag q1))
  (let-match erased (add-fn rhs K5 bc rhs2 p2 (add-comm K5 rhs rhs2 ar2)) (Refl _ _))
  (MkEulerSum kc D K3 K2 rhs gen c2 lhs2 K5 rhs2 g2 dc al2 a35 ar2 dg q2))


(def-fns _ $ (erased sized-blens : (erased (Nat) d m K) (erased (List (Blk)) s) (subterm erased (Sized d s) sz) (erased (Length (Blk) s m) ls)
    (erased (At d m (Zero) K) a) -> (erased (BLens s K) r))
  (let-match erased sz (SizedCons _ o p s1 lp sz1) ((SizedNil _) (let-match erased ls (LengthNil _)) (let-match erased a (AtZ _ _)) (BLenNil)))
  (let-match erased ls (LengthCons _ _ _ m1 ls1))
  (let-match erased a (AtS _ _ _ K1 _ a1 ad))
  (BLenCons s1 o d K1 K p lp (sized-blens d m1 K1 s1 sz1 ls1 a1) ad))


; The cube has 3 d edges.
(def-fns _ $ (erased cube-edges : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu)
    -> (erased (Nat) K) (erased (At d tg3 (Zero) K) aK) (erased (Orbits D ce K) r))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased (facts d e n f ids nf ni fi io rnf pe pn pf) (MkFacts _ _ _ _ _ _ _ _ RI Rne Ren _ _ _ _ _ _ _ _ _ _ Ridnf Ride _ _ lid lde _ _ lnf _ _ ue _ _ unf _ uid _))
  (let ((erased K) (erased aK)) (at-exists d tg3 (Zero)))
  (let-match erased le (MkLaid _ _ _ lyp szp))
  (let ((erased gp) (erased gr)) (graph-exists D ce (lay-length d tg6 D _ ce lyp szp (six _ _ _ _ _ _) aD)))
  (let ((erased lab) (erased ll)) (laid-exists d _ (SizedCons _ (Zero) _ _ lid $ SizedCons _ tg1 _ _ lid $ SizedCons _ tg2 _ _ lid $ SizedCons _ tg1 _ _ lnf $ SizedCons _ tg2 _ _ lde $ SizedCons _ (Zero) _ _ lid $ SizedNil d)))
  (let-match erased ll (MkLaid _ _ _ lyl szl))
  (let ((erased sr)) (Cons _ (MkBlk (Zero) ids) $ Cons _ (MkBlk tg1 ids) $ Cons _ (MkBlk tg2 ids) $ Nil (Blk)))
  (let ((erased rs) (erased lr)) (lay-exists d sr))
  (let ((erased I0) (erased s0)) (shf-exists d (Zero) ids))
  (let ((erased I1) (erased s1)) (shf-exists d tg1 ids))
  (let ((erased I2) (erased s2)) (shf-exists d tg2 ids))
  (let ((erased I3) (erased s3)) (shf-exists d tg3 ids))
  (let ((erased I4) (erased s4)) (shf-exists d tg4 ids))
  (let ((erased I5) (erased s5)) (shf-exists d tg5 ids))
  (let ((erased X) (erased sX)) (shf-exists d tg1 nf))
  (let ((erased Y) (erased sY)) (shf-exists d tg2 e))
  (let ((erased dids)) (iota-distinct d ids io))
  (let ((erased kp)) (lay-respects d _ _ _ lab ce lab lyl szl lyp lyl
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ren $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) Ridnf $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ride $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RI $
      LRNil _)))
  (let ((erased cl)) (resp-const D lab ce gp (graph-fun D ce gp gr) kp (lay-length d tg6 D _ lab lyl szl (six _ _ _ _ _ _) aD)))
  (values K aK (MkOrbits D K ce gp gr (lay-classes _ _ _ _ _ _ _ _ _ _ _ ll (six _ _ _ _ _ _) aD lr
    (SpreadCons _ _ _ _ dids uid (AvCons _ _ _ _ (ApLt _ _ _ _ (LtZ _)) $ AvCons _ _ _ _ (ApLt _ _ _ _ (LtZ _)) $ AvNil _) $
      SpreadCons _ _ _ _ dids uid (AvCons _ _ _ _ (ApLt _ _ _ _ (LtS _ _ (LtZ _))) $ AvNil _) $
      SpreadCons _ _ _ _ dids uid (AvNil _) $
      SpreadNil d)
    (sized-blens d tg3 K sr (SizedCons _ (Zero) _ _ lid $ SizedCons _ tg1 _ _ lid $ SizedCons _ tg2 _ _ lid $ SizedNil d) (LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthNil _) aK) li ioD
    (LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRNil _)
    cl
    (LSCons _ _ _ _ _ _ (NthHere _ _ _) (sub-refl ids) $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) (sub-refl ids) $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) (sub-refl ids) $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) (under-sub d nf ids unf io) $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) (under-sub d e ids ue io) $
      LSCons _ _ _ _ _ _ (NthHere _ _ _) (sub-refl ids) $
      LSNil _)
    (LLCons _ _ _ _ _ _ _ _ _ _ s0 s0 (link-refl gp I0) $
      LLCons _ _ _ _ _ _ _ _ _ _ s1 s1 (link-refl gp I1) $
      LLCons _ _ _ _ _ _ _ _ _ _ s2 s2 (link-refl gp I2) $
      LLCons _ _ _ _ _ _ _ _ _ _ sX s3 (blk-step _ _ _ _ _ _ _ _ _ _ _ _ le gr (NthThere _ _ _ _ _ $ NthHere _ _ _) Ren sX s3) $
      LLCons _ _ _ _ _ _ _ _ _ _ sY s4 (blk-step _ _ _ _ _ _ _ _ _ _ _ _ le gr (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne sY s4) $
      LLCons _ _ _ _ _ _ _ _ _ _ s0 s5 (blk-step _ _ _ _ _ _ _ _ _ _ _ _ le gr (NthHere _ _ _) RI s0 s5) $
      LLNil d gp)))))


; The cube has 2 d nodes.
(def-fns _ $ (erased cube-nodes : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu)
    -> (erased (Nat) K) (erased (At d tg2 (Zero) K) aK) (erased (Orbits D cn K) r))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased (facts d e n f ids nf ni fi io rnf pe pn pf) (MkFacts _ _ _ _ _ _ _ _ RI Rne Ren _ _ Rnin Rnni _ Reid _ Ridni _ Rniid Ridnf _ _ _ lid _ _ _ lnf lni _ _ _ _ unf uni uid _))
  (let ((erased K) (erased aK)) (at-exists d tg2 (Zero)))
  (let-match erased ln (MkLaid _ _ _ lyp szp))
  (let ((erased gp) (erased gr)) (graph-exists D cn (lay-length d tg6 D _ cn lyp szp (six _ _ _ _ _ _) aD)))
  (let ((erased lab) (erased ll)) (laid-exists d _ (SizedCons _ (Zero) _ _ lid $ SizedCons _ (Zero) _ _ lni $ SizedCons _ tg2 _ _ lid $ SizedCons _ tg2 _ _ lnf $ SizedCons _ tg2 _ _ lid $ SizedCons _ (Zero) _ _ lni $ SizedNil d)))
  (let-match erased ll (MkLaid _ _ _ lyl szl))
  (let ((erased sr)) (Cons _ (MkBlk (Zero) ids) $ Cons _ (MkBlk tg2 ids) $ Nil (Blk)))
  (let ((erased rs) (erased lr)) (lay-exists d sr))
  (let ((erased I0) (erased s0)) (shf-exists d (Zero) ids))
  (let ((erased I1) (erased s1)) (shf-exists d tg1 ids))
  (let ((erased I2) (erased s2)) (shf-exists d tg2 ids))
  (let ((erased I3) (erased s3)) (shf-exists d tg3 ids))
  (let ((erased I4) (erased s4)) (shf-exists d tg4 ids))
  (let ((erased I5) (erased s5)) (shf-exists d tg5 ids))
  (let ((erased X) (erased sX)) (shf-exists d (Zero) ni))
  (let ((erased Y) (erased sY)) (shf-exists d tg2 nf))
  (let ((erased Z) (erased sZ)) (shf-exists d tg3 e))
  (let ((erased dids)) (iota-distinct d ids io))
  (let ((erased kp)) (lay-respects d _ _ _ lab cn lab lyl szl lyp lyl
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) Rnin $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rniid $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ridnf $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) Ridni $
      LRNil _)))
  (let ((erased cl)) (resp-const D lab cn gp (graph-fun D cn gp gr) kp (lay-length d tg6 D _ lab lyl szl (six _ _ _ _ _ _) aD)))
  (values K aK (MkOrbits D K cn gp gr (lay-classes _ _ _ _ _ _ _ _ _ _ _ ll (six _ _ _ _ _ _) aD lr
    (SpreadCons _ _ _ _ dids uid (AvCons _ _ _ _ (ApLt _ _ _ _ (LtZ _)) $ AvNil _) $
      SpreadCons _ _ _ _ dids uid (AvNil _) $
      SpreadNil d)
    (sized-blens d tg2 K sr (SizedCons _ (Zero) _ _ lid $ SizedCons _ tg2 _ _ lid $ SizedNil d) (LengthCons _ _ _ _ $ LengthCons _ _ _ _ $ LengthNil _) aK) li ioD
    (LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RI $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI $
      LRNil _)
    cl
    (LSCons _ _ _ _ _ _ (NthHere _ _ _) (sub-refl ids) $
      LSCons _ _ _ _ _ _ (NthHere _ _ _) (under-sub d ni ids uni io) $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) (sub-refl ids) $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) (under-sub d nf ids unf io) $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) (sub-refl ids) $
      LSCons _ _ _ _ _ _ (NthHere _ _ _) (under-sub d ni ids uni io) $
      LSNil _)
    (LLCons _ _ _ _ _ _ _ _ _ _ s0 s0 (link-refl gp I0) $
      LLCons _ _ _ _ _ _ _ _ _ _ sX s1 (blk-step _ _ _ _ _ _ _ _ _ _ _ _ ln gr (NthHere _ _ _) Rnni sX s1) $
      LLCons _ _ _ _ _ _ _ _ _ _ s2 s2 (link-refl gp I2) $
      LLCons _ _ _ _ _ _ _ _ _ _ sY s3 (blk-step _ _ _ _ _ _ _ _ _ _ _ _ ln gr (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ren sY s3) $
      LLCons _ _ _ _ _ _ _ _ _ _ s2 s4 (link-trans gp _ _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ ln gr (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Reid s2 sZ) (blk-step _ _ _ _ _ _ _ _ _ _ _ _ ln gr (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rne sZ s4)) $
      LLCons _ _ _ _ _ _ _ _ _ _ sX s5 (link-trans gp _ _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ ln gr (NthHere _ _ _) Rnni sX s1) (blk-step _ _ _ _ _ _ _ _ _ _ _ _ ln gr (NthThere _ _ _ _ _ $ NthHere _ _ _) RI s1 s5)) $
      LLNil d gp)))))


(def-fns _ $ (erased graph-zip : (erased (Nat) d) (erased (List (Nat)) p ids) (erased (List (Bond)) g) (erased (Graph d p g) gr) (erased (Iota d ids) io)
    -> (erased (Zip ids p g) z))
  (let-match erased gr (MkGraph _ _ ids2 _ io2 lp z))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  z)

; The face labelling of the cube: blocks 0 to 3 of a dart x take the face label of x, block 4 its edge label and block 5
; its node label. It is constant along the cube's faces.
(def-fns _ $ (erased face-lab : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu) (erased (List (Nat)) labE labN labF) (erased (List (Bond)) ge gn gf gcf)
    (erased (Graph d e ge) gre) (erased (Graph d n gn) grn) (erased (Graph d f gf) grf) (erased (Const labE ge) clE) (erased (Const labN gn) clN)
    (erased (Const labF gf) clF) (erased (Length (Nat) labE d) llE) (erased (Length (Nat) labN d) llN) (erased (Length (Nat) labF d) llF)
    (erased (Graph D cf gcf) grc) -> (erased (List (Nat)) lab) (erased (Laid d (Cons (Blk) (MkBlk (Zero) labF) $ Cons (Blk) (MkBlk (Zero) labF) $ Cons (Blk) (MkBlk (Zero) labF) $ Cons (Blk) (MkBlk (Zero) labF) $ Cons (Blk) (MkBlk tg4 labE) $ Cons (Blk) (MkBlk tg5 labN) $ Nil (Blk)) lab) ll) (erased (Const lab gcf) cl))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased lf (MkLaid _ _ _ lyf szf))
  (let ((erased lab) (erased ll)) (laid-exists d _ (SizedCons _ (Zero) _ _ llF $ SizedCons _ (Zero) _ _ llF $ SizedCons _ (Zero) _ _ llF $ SizedCons _ (Zero) _ _ llF $ SizedCons _ tg4 _ _ llE $ SizedCons _ tg5 _ _ llN $ SizedNil d)))
  (let-match erased ll (MkLaid _ _ _ lyl szl))
  (let ((erased RF)) (respects-id-right d ids labF io llF))
  (let ((erased kp)) (lay-respects d _ _ _ lab cf lab lyl szl lyf lyl
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) RF $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RF $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RF $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) (graph-resp d f labF gf grf clF llF) $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) (graph-resp d e labE ge gre clE llE) $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) (graph-resp d n labN gn grn clN llN) $
      LRNil _)))
  (values lab ll (resp-const D lab cf gcf (graph-fun D cf gcf grc) kp (lay-length d tg6 D _ lab lyl szl (six _ _ _ _ _ _) aD))))


; The faces of the cube are those of the map, then its edges, then its nodes.
(def-fns _ $ (erased cube-faces : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu) (erased (Nat) ke kn kf) (erased (Orbits d e ke) oE) (erased (Orbits d n kn) oN) (erased (Orbits d f kf) oF)
    -> (erased (Nat) a kF) (erased (Add kn kf a) a1) (erased (Add ke a kF) a0) (erased (Orbits D cf kF) r))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased (facts d e n f ids nf ni fi io rnf pe pn pf) (MkFacts _ _ _ _ _ _ _ _ RI _ _ _ _ _ _ _ Reid _ _ _ _ _ _ Rnid Rfid _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  (let-match erased oE (MkOrbits _ _ _ gE grE csE))
  (let-match erased csE (MkClasses _ _ _ idsE labE rsE ioE llE lrE drE fixE clE roE))
  (let-match erased (iota-fn d ids idsE io ioE) (Refl _ _))
  (let-match erased oN (MkOrbits _ _ _ gN grN csN))
  (let-match erased csN (MkClasses _ _ _ idsN labN rsN ioN llN lrN drN fixN clN roN))
  (let-match erased (iota-fn d ids idsN io ioN) (Refl _ _))
  (let-match erased oF (MkOrbits _ _ _ gF grF csF))
  (let-match erased csF (MkClasses _ _ _ idsF labF rsF ioF llF lrF drF fixF clF roF))
  (let-match erased (iota-fn d ids idsF io ioF) (Refl _ _))
  (let-match erased lf (MkLaid _ _ _ lyf szf))
  (let ((erased gc) (erased grc)) (graph-exists D cf (lay-length d tg6 D _ cf lyf szf (six _ _ _ _ _ _) aD)))
  (let ((erased lab) (erased ll) (erased cl)) (face-lab d D e n f ce cn cf cu labE labN labF gE gN gF gc grE grN grF clE clN clF llE llN llF grc))
  (let ((erased a) (erased a1)) (add kn kf))
  (let ((erased kF) (erased a0)) (add ke a))
  (let ((erased sr)) (Cons _ (MkBlk tg4 rsE) $ Cons _ (MkBlk tg5 rsN) $ Cons _ (MkBlk (Zero) rsF) $ Nil (Blk)))
  (let ((erased rs) (erased lr)) (lay-exists d sr))
  (let ((erased I0) (erased s0)) (shf-exists d (Zero) ids))
  (let ((erased I1) (erased s1)) (shf-exists d tg1 ids))
  (let ((erased I2) (erased s2)) (shf-exists d tg2 ids))
  (let ((erased I3) (erased s3)) (shf-exists d tg3 ids))
  (let ((erased I4) (erased s4)) (shf-exists d tg4 ids))
  (let ((erased I5) (erased s5)) (shf-exists d tg5 ids))
  (let ((erased LF0) (erased sLF)) (shf-exists d (Zero) labF))
  (let ((erased LE4) (erased sLE)) (shf-exists d tg4 labE))
  (let ((erased LN5) (erased sLN)) (shf-exists d tg5 labN))
  (let ((erased F0) (erased sF0)) (shf-exists d (Zero) f))
  (let ((erased E4) (erased sE4)) (shf-exists d tg4 e))
  (let ((erased N5) (erased sN5)) (shf-exists d tg5 n))
  (let ((erased LkE) (erased SE)) (rooted-link gE rsE ids labE roE))
  (let ((erased LkN) (erased SN)) (rooted-link gN rsN ids labN roN))
  (let ((erased LkF) (erased SF)) (rooted-link gF rsF ids labF roF))
  (let ((erased k01)) (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grc (NthHere _ _ _) RI s0 s1))
  (let ((erased k12)) (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grc (NthThere _ _ _ _ _ $ NthHere _ _ _) RI s1 s2))
  (let ((erased k23)) (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grc (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI s2 s3))
  (let ((erased LF)) (link-lift gF gc d (Zero) labF ids LF0 I0 LkF
    (lift-zip gF gc d (Zero) ids f I0 F0 (graph-zip d f ids gF grF io) s0 sF0 (link-trans gc _ _ _ k01 (link-trans gc _ _ _ k12 (link-trans gc _ _ _ k23 (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grc (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rfid s3 sF0))))) sLF s0))
  (values a kF a1 a0 (MkOrbits D kF cf gc grc (lay-classes _ _ _ _ _ _ _ _ _ _ _ ll (six _ _ _ _ _ _) aD lr
    (SpreadCons _ _ _ _ drE (respects-under labE rsE rsE d fixE llE) (AvCons _ _ _ _ (ApLt _ _ _ _ (LtS _ _ (LtS _ _ (LtS _ _ (LtS _ _ (LtZ _)))))) $ AvCons _ _ _ _ (ApGt _ _ _ _ (LtZ _)) $ AvNil _) $
      SpreadCons _ _ _ _ drN (respects-under labN rsN rsN d fixN llN) (AvCons _ _ _ _ (ApGt _ _ _ _ (LtZ _)) $ AvNil _) $
      SpreadCons _ _ _ _ drF (respects-under labF rsF rsF d fixF llF) (AvNil _) $
      SpreadNil d)
    (BLenCons _ _ ke a kF _ lrE (BLenCons _ _ kn kf a _ lrN (BLenCons _ _ kf (Zero) kf _ lrF (BLenNil) (add-zero-right kf)) a1) a0) li ioD
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) fixE $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) fixN $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) fixF $
      LRNil _)
    cl
    (LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) SF $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) SF $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) SF $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) SF $
      LSCons _ _ _ _ _ _ (NthHere _ _ _) SE $
      LSCons _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) SN $
      LSNil _)
    (LLCons _ _ _ _ _ _ _ _ _ _ sLF s0 LF $
      LLCons _ _ _ _ _ _ _ _ _ _ sLF s1 (link-trans gc _ _ _ LF k01) $
      LLCons _ _ _ _ _ _ _ _ _ _ sLF s2 (link-trans gc _ _ _ LF (link-trans gc _ _ _ k01 k12)) $
      LLCons _ _ _ _ _ _ _ _ _ _ sLF s3 (link-trans gc _ _ _ LF (link-trans gc _ _ _ k01 (link-trans gc _ _ _ k12 k23))) $
      LLCons _ _ _ _ _ _ _ _ _ _ sLE s4 (link-lift gE gc d tg4 labE ids LE4 I4 LkE (lift-zip gE gc d tg4 ids e I4 E4 (graph-zip d e ids gE grE io) s4 sE4 (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grc (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Reid s4 sE4)) sLE s4) $
      LLCons _ _ _ _ _ _ _ _ _ _ sLN s5 (link-lift gN gc d tg5 labN ids LN5 I5 LkN (lift-zip gN gc d tg5 ids n I5 N5 (graph-zip d n ids gN grN io) s5 sN5 (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grc (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rnid s5 sN5)) sLN s5) $
      LLNil d gc)))))


; The cube's glink classes are those of the map: every dart of the cube is joined to block 0 of its dart of the map.
(def-fns _ $ (erased cube-glink : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu) (erased (Nat) kc) (erased (List (Bond)) gG) (erased (Glink d e n f gG) glG) (erased (Classes gG d kc) csG)
    -> (erased (List (Bond)) gC) (erased (Glink D ce cn cf gC) glC) (erased (Classes gC D kc) r))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased (facts d e n f ids nf ni fi io rnf pe pn pf) (MkFacts _ _ _ _ _ _ _ _ RI _ _ _ _ _ _ _ Reid _ _ Ridn _ _ Ride Rnid Rfid _ _ _ _ _ _ _ _ _ _ _ _ _ _))
  (let-match erased le (MkLaid _ _ _ lye sze))
  (let-match erased ln (MkLaid _ _ _ lyn szn))
  (let-match erased lf (MkLaid _ _ _ lyf szf))
  (let ((erased gce) (erased grce)) (graph-exists D ce (lay-length d tg6 D _ ce lye sze (six _ _ _ _ _ _) aD)))
  (let ((erased gcn) (erased grcn)) (graph-exists D cn (lay-length d tg6 D _ cn lyn szn (six _ _ _ _ _ _) aD)))
  (let ((erased gcf) (erased grcf)) (graph-exists D cf (lay-length d tg6 D _ cf lyf szf (six _ _ _ _ _ _) aD)))
  (let ((erased gcnf) (erased catnf)) (cat-exists gcn gcf))
  (let ((erased gC) (erased cat)) (cat-exists gce gcnf))
  (let ((erased glC)) (MkGlink D ce cn cf gce gcn gcf gcnf gC grce grcn grcf catnf cat))
  (let ((erased spE) (erased spN) (erased spF)) (glink-spans D ce cn cf gce gcn gcf gC glC grce grcn grcf))
  (let-match erased glG (MkGlink _ _ _ _ ge gn gf gnf _ gre grn grf c1 c2))
  (let-match erased csG (MkClasses _ _ _ idsG labG rsG ioG llG lrG drG fixG clG roG))
  (let-match erased (iota-fn d ids idsG io ioG) (Refl _ _))
  (let ((erased sGe) (erased sGn) (erased sGf)) (glink-spans d e n f ge gn gf gG glG gre grn grf))
  (let ((erased RGe)) (graph-resp d e labG ge gre (const-spans labG gG ge d clG llG sGe (graph-below d e nf ge (graph-fun d e ge gre) pe)) llG))
  (let ((erased cGn)) (const-spans labG gG gn d clG llG sGn (graph-below d n ni gn (graph-fun d n gn grn) pn)))
  (let ((erased RGn)) (graph-resp d n labG gn grn cGn llG))
  (let ((erased RGf)) (graph-resp d f labG gf grf (const-spans labG gG gf d clG llG sGf (graph-below d f fi gf (graph-fun d f gf grf) pf)) llG))
  (let ((erased RGnf)) (respects-assoc-inv f n labG nf labG labG rnf RGf RGn))
  (let ((erased gni) (erased grni)) (perm-graph d ni n (perm-sym d n ni pn)))
  (let ((erased RGni)) (graph-resp d ni labG gni grni (const-inv d labG n ni gn gni (graph-fun d ni gni grni) (perm-sym d n ni pn) grn cGn) llG))
  (let ((erased RGid)) (respects-id-right d ids labG io llG))
  (let ((erased lab) (erased ll)) (laid-exists d _ (SizedCons _ (Zero) _ _ llG $ SizedCons _ (Zero) _ _ llG $ SizedCons _ (Zero) _ _ llG $ SizedCons _ (Zero) _ _ llG $ SizedCons _ (Zero) _ _ llG $ SizedCons _ (Zero) _ _ llG $ SizedNil d)))
  (let-match erased ll (MkLaid _ _ _ lyl szl))
  (let ((erased lD)) (lay-length d tg6 D _ lab lyl szl (six _ _ _ _ _ _) aD))
  (let ((erased cle)) (resp-const D lab ce gce (graph-fun D ce gce grce) (lay-respects d _ _ _ lab ce lab lyl szl lye lyl
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGid $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGe $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGnf $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) RGnf $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGe $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RGid $
      LRNil _)) lD))
  (let ((erased cln)) (resp-const D lab cn gcn (graph-fun D cn gcn grcn) (lay-respects d _ _ _ lab cn lab lyl szl lyn lyl
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) RGn $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGid $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGe $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGnf $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGid $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RGni $
      LRNil _)) lD))
  (let ((erased clf)) (resp-const D lab cf gcf (graph-fun D cf gcf grcf) (lay-respects d _ _ _ lab cf lab lyl szl lyf lyl
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) RGid $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGid $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGid $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RGf $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGe $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RGn $
      LRNil _)) lD))
  (let ((erased cl)) (const-cat lab gce gcnf gC cat cle (const-cat lab gcn gcf gcnf catnf cln clf)))
  (let ((erased sr)) (Cons _ (MkBlk (Zero) rsG) $ Nil (Blk)))
  (let ((erased rs) (erased lr)) (lay-exists d sr))
  (let ((erased I0) (erased s0)) (shf-exists d (Zero) ids))
  (let ((erased I1) (erased s1)) (shf-exists d tg1 ids))
  (let ((erased I2) (erased s2)) (shf-exists d tg2 ids))
  (let ((erased I3) (erased s3)) (shf-exists d tg3 ids))
  (let ((erased I4) (erased s4)) (shf-exists d tg4 ids))
  (let ((erased I5) (erased s5)) (shf-exists d tg5 ids))
  (let ((erased LG0) (erased sLG)) (shf-exists d (Zero) labG))
  (let ((erased E0) (erased sE0)) (shf-exists d (Zero) e))
  (let ((erased E1) (erased sE1)) (shf-exists d tg1 e))
  (let ((erased E2) (erased sE2)) (shf-exists d tg2 e))
  (let ((erased E3) (erased sE3)) (shf-exists d tg3 e))
  (let ((erased Nb0) (erased sN0)) (shf-exists d (Zero) n))
  (let ((erased Nb1) (erased sN1)) (shf-exists d tg1 n))
  (let ((erased F0) (erased sF0)) (shf-exists d (Zero) f))
  (let ((erased LkG) (erased SG)) (rooted-link gG rsG ids labG roG))
  (let ((erased k01)) (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthHere _ _ _) RI s0 s1) spF))
  (let ((erased k12)) (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthThere _ _ _ _ _ $ NthHere _ _ _) RI s1 s2) spF))
  (let ((erased k23)) (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI s2 s3) spF))
  (let ((erased LIE)) (link-trans gC _ _ _ k01 (link-trans gC _ _ _ (link-spans gce gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ le grce (NthThere _ _ _ _ _ $ NthHere _ _ _) Reid s1 sE3) spE) (link-sym gC _ _ (link-trans gC _ _ _ (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthHere _ _ _) Ride sE0 sE1) spF) (link-trans gC _ _ _ (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthThere _ _ _ _ _ $ NthHere _ _ _) Ride sE1 sE2) spF) (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ride sE2 sE3) spF)))))))
  (let ((erased LIN)) (link-trans gC _ _ _ (link-spans gcn gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ ln grcn (NthHere _ _ _) Rnid s0 sN1) spN) (link-sym gC _ _ (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthHere _ _ _) Ridn sN0 sN1) spF))))
  (let ((erased LIF)) (link-trans gC _ _ _ k01 (link-trans gC _ _ _ k12 (link-trans gC _ _ _ k23 (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rfid s3 sF0) spF)))))
  (let ((erased LG)) (link-lift gG gC d (Zero) labG ids LG0 I0 LkG
    (lift-cat ge gnf gG gC d (Zero) c2 (lift-zip ge gC d (Zero) ids e I0 E0 (graph-zip d e ids ge gre io) s0 sE0 LIE)
      (lift-cat gn gf gnf gC d (Zero) c1 (lift-zip gn gC d (Zero) ids n I0 Nb0 (graph-zip d n ids gn grn io) s0 sN0 LIN)
        (lift-zip gf gC d (Zero) ids f I0 F0 (graph-zip d f ids gf grf io) s0 sF0 LIF)))
    sLG s0))
  (values gC glC (lay-classes _ _ _ _ _ _ _ _ _ _ _ ll (six _ _ _ _ _ _) aD lr
    (SpreadCons _ _ _ _ drG (respects-under labG rsG rsG d fixG llG) (AvNil _) $
      SpreadNil d)
    (BLenCons _ _ kc (Zero) kc _ lrG (BLenNil) (add-zero-right kc)) li ioD
    (LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) fixG $
      LRNil _)
    cl
    (LSCons _ _ _ _ _ _ (NthHere _ _ _) SG $
      LSCons _ _ _ _ _ _ (NthHere _ _ _) SG $
      LSCons _ _ _ _ _ _ (NthHere _ _ _) SG $
      LSCons _ _ _ _ _ _ (NthHere _ _ _) SG $
      LSCons _ _ _ _ _ _ (NthHere _ _ _) SG $
      LSCons _ _ _ _ _ _ (NthHere _ _ _) SG $
      LSNil _)
    (LLCons _ _ _ _ _ _ _ _ _ _ sLG s0 LG $
      LLCons _ _ _ _ _ _ _ _ _ _ sLG s1 (link-trans gC _ _ _ LG k01) $
      LLCons _ _ _ _ _ _ _ _ _ _ sLG s2 (link-trans gC _ _ _ LG (link-trans gC _ _ _ k01 k12)) $
      LLCons _ _ _ _ _ _ _ _ _ _ sLG s3 (link-trans gC _ _ _ LG (link-trans gC _ _ _ k01 (link-trans gC _ _ _ k12 k23))) $
      LLCons _ _ _ _ _ _ _ _ _ _ sLG s4 (link-trans gC _ _ _ LG (link-trans gC _ _ _ LIE (link-trans gC _ _ _ (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthHere _ _ _) Ride sE0 sE1) spF) (link-trans gC _ _ _ (link-spans gcf gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ lf grcf (NthThere _ _ _ _ _ $ NthHere _ _ _) Ride sE1 sE2) spF) (link-sym gC _ _ (link-spans gce gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ le grce (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Reid s4 sE2) spE)))))) $
      LLCons _ _ _ _ _ _ _ _ _ _ sLG s5 (link-trans gC _ _ _ LG (link-spans gce gC _ _ (blk-step _ _ _ _ _ _ _ _ _ _ _ _ le grce (NthHere _ _ _) RI s0 s5) spE)) $
      LLNil d gC))))


; The cube has the genus of the map.
(def-fns _ $ (erased cube-genus : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu) (erased (Nat) gen) (erased (Genus d e n f gen) g)
    -> (erased (Genus D ce cn cf gen) r))
  (let ((erased kc) (erased ke) (erased kn) (erased kf) (erased gG) (erased oe) (erased on) (erased of) (erased gl) (erased cc) (erased es))
    (genus-parts d gen e n f g))
  (let ((erased K3) (erased a3) (erased oce)) (cube-edges d D e n f ce cn cf cu))
  (let ((erased K2) (erased a2) (erased ocn)) (cube-nodes d D e n f ce cn cf cu))
  (let ((erased a) (erased kF) (erased a1) (erased a0) (erased ocf)) (cube-faces d D e n f ce cn cf cu ke kn kf oe on of))
  (let ((erased gC) (erased glC) (erased ccC)) (cube-glink d D e n f ce cn cf cu kc gG gl cc))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (genus-make D gen kc K3 K2 kF ce cn cf gC oce ocn ocf glC ccC (es-cube kc d ke kn kf gen D K3 K2 a kF es aD a3 a2 a1 a0)))


(def-fns _ $ (erased shf-under : (erased (Nat) d o m D) (erased (List (Nat)) P B) (subterm erased (Shf d o P B) sh) (erased (Under P d) up)
    (erased (At d m (Zero) D) aD) (erased (Lt o m) lt) -> (erased (Under B D) r))
  (let-match erased sh (ShfCons _ _ y z P1 Bs1 a sh1) ((ShfNil _ _) (UnderNil D)))
  (let-match erased up (UnderCons _ _ _ ly up1))
  (UnderCons Bs1 z D (at-lt d o y z m D a aD ly lt) (shf-under d o m D P1 Bs1 sh1 up1 aD lt)))

; The cube of a bridgeless map is bridgeless: under the face labelling, the two ends of each edge of the cube differ.
(def-fns _ $ (erased cube-bridgeless : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu) (erased (Bridgeless d e n f) b) -> (erased (Bridgeless D ce cn cf) r))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased (facts d e n f ids nf ni fi io rnf pe pn pf) (MkFacts _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lde _ _ lnf _ _ ue _ _ unf _ uid _))
  (let ((erased kE) (erased oE)) (orbits-exists d e nf pe))
  (let-match erased oE (MkOrbits _ _ _ gE grE csE))
  (let-match erased csE (MkClasses _ _ _ idsE labE rsE ioE llE lrE drE fixE clE roE))
  (let-match erased (iota-fn d ids idsE io ioE) (Refl _ _))
  (let ((erased uE)) (rooted-under gE rsE ids labE labE d roE fixE llE))
  (let ((erased kN) (erased oN)) (orbits-exists d n ni pn))
  (let-match erased oN (MkOrbits _ _ _ gN grN csN))
  (let-match erased csN (MkClasses _ _ _ idsN labN rsN ioN llN lrN drN fixN clN roN))
  (let-match erased (iota-fn d ids idsN io ioN) (Refl _ _))
  (let ((erased uN)) (rooted-under gN rsN ids labN labN d roN fixN llN))
  (let ((erased kF) (erased oF)) (orbits-exists d f fi pf))
  (let-match erased oF (MkOrbits _ _ _ gF grF csF))
  (let-match erased csF (MkClasses _ _ _ idsF labF rsF ioF llF lrF drF fixF clF roF))
  (let-match erased (iota-fn d ids idsF io ioF) (Refl _ _))
  (let ((erased uF)) (rooted-under gF rsF ids labF labF d roF fixF llF))
  (let-match erased le (MkLaid _ _ _ lye sze))
  (let-match erased lf (MkLaid _ _ _ lyf szf))
  (let ((erased gce) (erased grce)) (graph-exists D ce (lay-length d tg6 D _ ce lye sze (six _ _ _ _ _ _) aD)))
  (let ((erased gcf) (erased grcf)) (graph-exists D cf (lay-length d tg6 D _ cf lyf szf (six _ _ _ _ _ _) aD)))
  (let ((erased lab) (erased ll) (erased cl)) (face-lab d D e n f ce cn cf cu labE labN labF gE gN gF gcf grE grN grF clE clN clF llE llN llF grcf))
  (let-match erased ll (MkLaid _ _ _ lyl szl))
  (let-match erased b (MkBridgeless _ _ _ _ ge2 gf2 pe2 pf2 sp))
  (let-match erased (graph-fn d e ge2 gE pe2 grE) (Refl _ _))
  (let-match erased (graph-fn d f gf2 gF pf2 grF) (Refl _ _))
  (let ((erased lFe) (erased rFe)) (respects-exists labF e d ue llF))
  (let ((erased lFnf) (erased rFnf)) (respects-exists labF nf d unf llF))
  (let ((erased lEnf) (erased rEnf)) (respects-exists labE nf d unf llE))
  (let ((erased RF)) (respects-id-right d ids labF io llF))
  (let ((erased gnf) (erased grnf)) (perm-graph d nf e (perm-sym d e nf pe)))
  (let ((erased dFe)) (allsep-differ d ids e labF lFe ids labF rsF gE gF (graph-zip d e ids gE grE io) sp RF rFe uid ue io roF))
  (let ((erased dFnf)) (allsep-differ d ids nf labF lFnf ids labF rsF gnf gF (graph-zip d nf ids gnf grnf io)
    (allsep-inv d e nf gE gnf gF (graph-fun d nf gnf grnf) (perm-sym d e nf pe) grE sp) RF rFnf uid unf io roF))
  (let ((erased sy)) (Cons _ (MkBlk tg5 labN) $ Cons _ (MkBlk (Zero) lFe) $ Cons _ (MkBlk tg4 lEnf) $ Cons _ (MkBlk (Zero) lFnf) $
    Cons _ (MkBlk (Zero) lFe) $ Cons _ (MkBlk (Zero) labF) $ Nil (Blk)))
  (let ((erased LY) (erased lyY)) (lay-exists d sy))
  (let ((erased rY)) (lay-respects d _ _ _ lab ce LY lyl szl lye lyY
    (LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) (respects-id-right d ids labN io llN) $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) rFe $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) rEnf $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthHere _ _ _) rFnf $
      LRCons _ _ _ _ _ _ _ _ (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) rFe $
      LRCons _ _ _ _ _ _ _ _ (NthHere _ _ _) RF $
      LRNil _)))
  (let ((erased lFeL) (erased uFe)) (values (respects-length labF e lFe d rFe lde) (respects-under-out labF e lFe d rFe uF)))
  (let ((erased dif)) (lay-differ d _ _ lab LY lyl lyY
    (LDCons _ _ _ _ _ _ _ llF llN uF uN (OrL _ _ (ApLt _ _ _ _ (LtZ _))) $
      LDCons _ _ _ _ _ _ _ llF lFeL uF uFe (OrR _ _ dFe) $
      LDCons _ _ _ _ _ _ _ llF (respects-length labE nf lEnf d rEnf lnf) uF (respects-under-out labE nf lEnf d rEnf uE) (OrL _ _ (ApLt _ _ _ _ (LtZ _))) $
      LDCons _ _ _ _ _ _ _ llF (respects-length labF nf lFnf d rFnf lnf) uF (respects-under-out labF nf lFnf d rFnf uF) (OrR _ _ dFnf) $
      LDCons _ _ _ _ _ _ _ llE lFeL uE uFe (OrL _ _ (ApGt _ _ _ _ (LtZ _))) $
      LDCons _ _ _ _ _ _ _ llN llF uN uF (OrL _ _ (ApGt _ _ _ _ (LtZ _))) $
      LDNil d)))
  (MkBridgeless D ce cn cf gce gcf grce grcf
    (allsep-of I ce lab LY lab gce gcf (graph-zip D ce I gce grce ioD)
      (respects-id-right D I lab ioD (lay-length d tg6 D _ lab lyl szl (six _ _ _ _ _ _) aD)) rY dif cl)))


; A four-colouring of the cube gives one of the map: each dart takes the colour of its copy in block 3.
(def-fns _ $ (erased cube-colorable : (erased (Nat) d D) (erased (List (Nat)) e n f ce cn cf) (erased (Cube d D e n f ce cn cf) cu) (erased (List (Nat)) K) (erased (FourColoring ce cf K) c)
    -> (erased (List (Nat)) ks) (erased (FourColoring e f ks) r))
  (let-match erased cu (MkCube _ _ _ _ _ ids nf ni fi _ _ _ cfi I io rnf pe pn pf aD ioD le ln lf lfi li))
  (let-match erased (facts d e n f ids nf ni fi io rnf pe pn pf) (MkFacts _ _ _ _ _ _ _ _ RI _ _ _ _ _ _ _ Reid _ _ _ _ _ _ _ Rfid lid _ _ _ _ _ _ ue _ uf _ _ uid _))
  (let-match erased le (MkLaid _ _ _ lye sze))
  (let-match erased lf (MkLaid _ _ _ lyf szf))
  (let-match erased c (MkFourColoring _ _ _ Ke rk rke dk uk))
  (let ((erased lK)) (respects-length K cf K D rk (lay-length d tg6 D _ cf lyf szf (six _ _ _ _ _ _) aD)))
  (let ((erased I1) (erased s1)) (shf-exists d tg1 ids))
  (let ((erased I2) (erased s2)) (shf-exists d tg2 ids))
  (let ((erased I3) (erased s3)) (shf-exists d tg3 ids))
  (let ((erased F0) (erased sF0)) (shf-exists d (Zero) f))
  (let ((erased F1) (erased sF1)) (shf-exists d tg1 f))
  (let ((erased F2) (erased sF2)) (shf-exists d tg2 f))
  (let ((erased F3) (erased sF3)) (shf-exists d tg3 f))
  (let ((erased E3) (erased sE3)) (shf-exists d tg3 e))
  (let ((erased u1) (erased u3)) (values (shf-under d tg1 tg6 D ids I1 s1 uid aD (LtS _ _ (LtZ _))) (shf-under d tg3 tg6 D ids I3 s3 uid aD (LtS _ _ (LtS _ _ (LtS _ _ (LtZ _)))))))
  (let ((erased lI3)) (shf-length d tg3 d ids I3 s3 lid))
  (let ((erased ks) (erased rks)) (respects-exists K I3 D u3 lK))
  (let ((erased lks)) (respects-length K I3 ks d rks lI3))
  (let ((erased Ridf)) (respects-id-left d ids f io uf))
  (let ((erased q0)) (const-step K cf I3 F0 ks rk (shf-respects d tg3 (Zero) _ cf _ _ _ _ _ lyf szf (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Rfid s3 sF0) rks))
  (let ((erased q1)) (const-step K cf F0 F1 ks rk (shf-respects d (Zero) tg1 _ cf _ _ _ _ _ lyf szf (NthHere _ _ _) Ridf sF0 sF1) q0))
  (let ((erased q2)) (const-step K cf F1 F2 ks rk (shf-respects d tg1 tg2 _ cf _ _ _ _ _ lyf szf (NthThere _ _ _ _ _ $ NthHere _ _ _) Ridf sF1 sF2) q1))
  (let ((erased q3)) (const-step K cf F2 F3 ks rk (shf-respects d tg2 tg3 _ cf _ _ _ _ _ lyf szf (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) Ridf sF2 sF3) q2))
  (let ((erased rf)) (respects-assoc f I3 K F3 ks ks d (shf-compose d tg3 ids f I3 F3 io s3 sF3 uf) q3 rks lks lI3))
  (let ((erased ke) (erased rke2)) (respects-exists ks e d ue lks))
  (let ((erased W) (erased rW)) (respects-exists K E3 D (shf-under d tg3 tg6 D e E3 sE3 ue aD (LtS _ _ (LtS _ _ (LtS _ _ (LtZ _))))) lK))
  (let-match erased (respects-fn ks e W ke (respects-assoc e I3 K E3 ks W d (shf-compose d tg3 ids e I3 E3 io s3 sE3 ue) rW rks lks lI3) rke2)
    (Refl _ _))
  (let ((erased rKe)) (respects-assoc I1 ce K E3 Ke W D (shf-respects d tg1 tg3 _ ce _ _ _ _ _ lye sze (NthThere _ _ _ _ _ $ NthHere _ _ _) Reid s1 sE3) rW rke
    (respects-length K ce Ke D rke (lay-length d tg6 D _ ce lye sze (six _ _ _ _ _ _) aD)) (lay-length d tg6 D _ ce lye sze (six _ _ _ _ _ _) aD)))
  (let ((erased Y1) (erased rY1)) (respects-exists K I1 D u1 lK))
  (let-match erased (respects-fn K I3 Y1 ks (const-step K cf I2 I3 Y1 rk (shf-respects d tg2 tg3 _ cf _ _ _ _ _ lyf szf (NthThere _ _ _ _ _ $ NthThere _ _ _ _ _ $ NthHere _ _ _) RI s2 s3) (const-step K cf I1 I2 Y1 rk (shf-respects d tg1 tg2 _ cf _ _ _ _ _ lyf szf (NthThere _ _ _ _ _ $ NthHere _ _ _) RI s1 s2) rY1)) rks) (Refl _ _))
  (values ks (MkFourColoring e f ks ke rf rke2 (differ-restrict Ke K I1 ke ks dk rKe rY1) (respects-under-out K I3 ks 4 rks uk))))

