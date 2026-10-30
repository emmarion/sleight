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
