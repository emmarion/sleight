; Hypermaps on the darts 0..d-1, after Gonthier and Werner's hypermap.v and geometry.v.

; The edge, node and face permutations e, n and f, with n (f (e x)) = x, f (e (n x)) = x and e (n (f x)) = x for every
; dart x (cancel3 edge node face, and its two rotations). fe, en and nf are the composites.
(def-adts $ (Hypermap : ((Nat) d) ((List (Nat)) e n f) -> Type)
  enum
  (many MkHypermap : (erased (Nat) d) (erased (List (Nat)) e n f ids fe en nf) (erased (Iota d ids) io)
      (erased (Respects f e fe) cfe) (erased (Respects n fe ids) ke)
      (erased (Respects e n en) cen) (erased (Respects f en ids) kn)
      (erased (Respects n f nf) cnf) (erased (Respects e nf ids) kf)
      -> (Hypermap d e n f)))

; gh is g followed by h.
(def-adts $ (Cat : ((List (Bond)) g h gh) -> Type)
  enum
  (many CatNil : (erased (List (Bond)) h) -> (Cat (Nil (Bond)) h h))
  (many CatCons : (erased (List (Bond)) g h gh) (erased (Bond) b) (erased (Cat g h gh) rest)
      -> (Cat (Cons (Bond) b g) h (Cons (Bond) b gh))))

; The bonds of glink: g lists those of the graphs of e, n and f.
(def-adts $ (Glink : ((Nat) d) ((List (Nat)) e n f) ((List (Bond)) g) -> Type)
  enum
  (many MkGlink : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Bond)) ge gn gf gnf g)
      (erased (Graph d e ge) pe) (erased (Graph d n gn) pn) (erased (Graph d f gf) pf)
      (erased (Cat gn gf gnf) c1) (erased (Cat ge gnf g) c2) -> (Glink d e n f g)))

; Euler_lhs = genus.*2 + Euler_rhs, with Euler_lhs = 2 * (number of glink components) + d and Euler_rhs the sum of the
; numbers of orbits of e, n and f (Gonthier's even_genus, read as the definition of the genus).
(def-adts $ (Genus : ((Nat) d) ((List (Nat)) e n f) ((Nat) gen) -> Type)
  enum
  (many MkGenus : (erased (Nat) d gen ke kn kf kc c2 lhs s1 rhs g2) (erased (List (Nat)) e n f) (erased (List (Bond)) g)
      (erased (Orbits d e ke) oe) (erased (Orbits d n kn) on) (erased (Orbits d f kf) of)
      (erased (Glink d e n f g) gl) (erased (Classes g d kc) cc)
      (erased (Double kc c2) dc) (erased (Add c2 d lhs) al) (erased (Add ke kn s1) a1) (erased (Add s1 kf rhs) ar)
      (erased (Double gen g2) dg) (erased (Add g2 rhs lhs) ag) -> (Genus d e n f gen)))

; Every bond x-y of g has x and y told apart in h.
(def-adts $ (AllSep : ((List (Bond)) h) ((List (Bond)) g) -> Type)
  enum
  (many AllSepNil : (erased (List (Bond)) h) -> (AllSep h (Nil (Bond))))
  (many AllSepCons : (erased (List (Bond)) h g) (erased (Nat) x y) (erased (Sep h x y) s) (erased (AllSep h g) rest)
      -> (AllSep h (Cons (Bond) (MkBond x y) g))))

; No dart is in the face orbit of its edge image.
(def-adts $ (Bridgeless : ((Nat) d) ((List (Nat)) e n f) -> Type)
  enum
  (many MkBridgeless : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Bond)) ge gf)
      (erased (Graph d e ge) pe) (erased (Graph d f gf) pf) (erased (AllSep gf ge) s) -> (Bridgeless d e n f)))

; The entries of xs and ys differ at each position.
(def-adts $ (Differ : ((List (Nat)) xs ys) -> Type)
  enum
  (many DifferNil : -> (Differ (Nil (Nat)) (Nil (Nat))))
  (many DifferCons : (erased (List (Nat)) xs ys) (erased (Nat) x y) (erased (Apart (Nat) Lt x y) ne) (erased (Differ xs ys) rest)
      -> (Differ (Cons (Nat) x xs) (Cons (Nat) y ys))))

; Every entry of ks is below b.
(def-adts $ (Under : ((List (Nat)) ks) ((Nat) b) -> Type)
  enum
  (many UnderNil : (erased (Nat) b) -> (Under (Nil (Nat)) b))
  (many UnderCons : (erased (List (Nat)) ks) (erased (Nat) k b) (erased (Lt k b) p) (erased (Under ks b) rest)
      -> (Under (Cons (Nat) k ks) b)))

; ks colours the darts so that each face has one colour and the two ends of each edge link differ (Gonthier's
; coloring of edge and face), with colours below 4.
(def-adts $ (FourColoring : ((List (Nat)) e f ks) -> Type)
  enum
  (many MkFourColoring : (erased (List (Nat)) e f ks ke) (erased (Respects ks f ks) face) (erased (Respects ks e ke) ce)
      (erased (Differ ke ks) edge) (erased (Under ks 4) four) -> (FourColoring e f ks)))

; (c . b) . a = c . (b . a).
(def-fns _ $ (erased respects-assoc : (erased (List (Nat)) a b c ba cb ls) (erased (Nat) d) (subterm erased (Respects b a ba) r1)
    (erased (Respects c ba ls) r2) (erased (Respects c b cb) r3) (erased (Length (Nat) cb d) lcb) (erased (Length (Nat) b d) lb)
    -> (erased (Respects cb a ls) r))
  (let-match erased r1 (RespCons _ a1 ba1 j l p r11) ((RespNil _) (let-match erased r2 (RespNil _)) (RespNil cb)))
  (let-match erased r2 (RespCons _ _ ls1 _ m q r21))
  (let ((erased w) (erased pw)) (nth-exists _ cb d j lcb (nth-lt-length _ b j d l p lb)))
  (let-match erased (nth-fn _ c l w m (respects-nth c b cb j l w r3 p pw) q) (Refl _ _))
  (RespCons cb a1 ls1 j w pw (respects-assoc a1 b c ba1 cb ls1 d r11 r21 r3 lcb lb)))

(def-fns _ $ (erased respects-exists : (erased (List (Nat)) a b) (erased (Nat) d)
    (subterm erased (Under b d) ub) (erased (Length (Nat) a d) la) -> (erased (List (Nat)) ab) (erased (Respects a b ab) rp))
  (let-match erased ub (UnderCons b1 j _ lj ub1) ((UnderNil _) (values (Nil _) (RespNil a))))
  (let ((erased w) (erased pw)) (nth-exists _ a d j la lj))
  (let ((erased ab1) (erased r1)) (respects-exists a b1 d ub1 la))
  (values (Cons _ w ab1) (RespCons a b1 ab1 j w pw r1)))

(def-fns _ $ (erased hyper-lengths : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h)
    -> (erased (Length (Nat) e d) le) (erased (Length (Nat) n d) ln) (erased (Length (Nat) f d) lf))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (let ((erased li)) (iota-length d ids io))
  (values (respects-length-inv f e fe d cfe (respects-length-inv n fe ids d ke li))
    (respects-length-inv e n en d cen (respects-length-inv f en ids d kn li))
    (respects-length-inv n f nf d cnf (respects-length-inv e nf ids d kf li))))

; The rotation (edge, node, face) to (node, face, edge): Gonthier's permN.
(def-fns _ $ (erased hyper-rot : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h) -> (erased (Hypermap d n f e) r))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (MkHypermap d n f e ids en nf fe io cen kn cnf kf cfe ke))

; The edge permutation has inverse n . f.
(def-fns _ $ (erased hyper-perm : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (Hypermap d e n f) h)
    -> (erased (List (Nat)) nf) (erased (Perm d e nf) pm))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (values nf (MkPerm d e nf ids io le
    (respects-assoc e f n fe nf ids d cfe ke cnf (respects-length-inv e nf ids d kf (iota-length d ids io)) lf) kf)))

(def-fns _ $ (erased colored-four : (erased (List (Nat)) ks e nd cs) (subterm erased (Colored ks e nd cs) c)
    -> (erased (List (Nat)) ke) (erased (Respects ks nd cs) rn) (erased (Respects ks e ke) re) (erased (Differ ke cs) df)
    (erased (Under cs 4) u))
  (let-match erased c (ColoredCons _ e1 nd1 cs1 a b k k2 bound node edge differ c1)
    ((ColoredNil _) (values (Nil _) (RespNil ks) (RespNil ks) (DifferNil) (UnderNil _))))
  (let ((erased ke1) (erased rn1) (erased re1) (erased df1) (erased u1)) (colored-four ks e1 nd1 cs1 c1))
  (values (Cons _ k2 ke1) (RespCons ks nd1 cs1 b k node rn1) (RespCons ks e1 ke1 a k2 edge re1)
    (DifferCons ke1 cs1 k2 k (apart-sym k k2 differ) df1) (UnderCons cs1 k _ bound u1)))

(def-fns _ $ (erased four-colored : (erased (List (Nat)) ks e nd cs ke) (subterm erased (Respects ks nd cs) rn) (erased (Respects ks e ke) re)
    (erased (Differ ke cs) df) (erased (Under cs 4) u) -> (erased (Colored ks e nd cs) c))
  (let-match erased rn (RespCons _ nd1 cs1 b k node rn1)
    ((RespNil _) (let-match erased df (DifferNil)) (let-match erased re (RespNil _)) (ColoredNil ks)))
  (let-match erased df (DifferCons _ _ _ _ ne df1))
  (let-match erased re (RespCons _ e1 ke1 a k2 edge re1))
  (let-match erased u (UnderCons _ _ _ bound u1))
  (ColoredCons ks e1 nd1 cs1 a b k k2 bound node edge (apart-sym k2 k ne) (four-colored ks e1 nd1 cs1 ke1 rn1 re1 df1 u1)))

; Colored of map.sl is a four-colouring of the hypermap with face nd.
(def-fns _ $ (erased colored-coloring : (erased (List (Nat)) ks e nd) (erased (Colored ks e nd ks) c) -> (erased (FourColoring e nd ks) r))
  (let ((erased ke) (erased rn) (erased re) (erased df) (erased u)) (colored-four ks e nd ks c))
  (MkFourColoring e nd ks ke rn re df u))

(def-fns _ $ (erased coloring-colored : (erased (List (Nat)) ks e nd) (erased (FourColoring e nd ks) c) -> (erased (Colored ks e nd ks) r))
  (let-match erased c (MkFourColoring _ _ _ ke rn re df u))
  (four-colored ks e nd ks ke rn re df u))

(def-fns _ $ (erased allsep-adj : (erased (List (Bond)) h g) (erased (Nat) x y) (subterm erased (Adj g x y) a) (erased (AllSep h g) s)
    -> (erased (Sep h x y) r))
  (match erased a _
    ((AdjFwd _ _ _) (let-match erased s (AllSepCons _ _ _ _ s1 _)) s1)
    ((AdjBwd _ _ _) (let-match erased s (AllSepCons _ _ _ _ s1 _)) (sep-sym h y x s1))
    ((AdjThere g1 _ _ _ a1) (let-match erased s (AllSepCons _ _ _ _ _ s2)) (allsep-adj h g1 x y a1 s2))))

; In a bridgeless hypermap no walk along the faces leads from a dart to its edge image.
(def-fns _ $ (erased absurd bridgeless-face : (erased (Nat) d x y) (erased (List (Nat)) e n f s xs) (erased (Bridgeless d e n f) b)
    (erased (Nth (Nat) e x y) px) (erased (Path f s x y xs) w) -> (erased (False) r))
  (let-match erased b (MkBridgeless _ _ _ _ ge gf pe pf sp))
  (sep-conn gf x y (allsep-adj gf ge x y (graph-adj d x y e ge pe px) sp) (path-graph-conn d x y f s xs gf w pf)))

(def-fns _ $ (erased adj-cat-l : (erased (List (Bond)) g h gh) (erased (Nat) x y) (subterm erased (Adj g x y) a) (erased (Cat g h gh) c)
    -> (erased (Adj gh x y) r))
  (let-match erased c (CatCons g1 _ gh1 b c1) (absurd (CatNil _) a))
  (match erased a _
    ((AdjFwd _ _ _) (AdjFwd gh1 x y))
    ((AdjBwd _ _ _) (AdjBwd gh1 y x))
    ((AdjThere _ _ _ _ a1) (AdjThere gh1 b x y (adj-cat-l g1 h gh1 x y a1 c1)))))

(def-fns _ $ (erased adj-cat-r : (erased (List (Bond)) g h gh) (erased (Nat) x y) (erased (Adj h x y) a) (subterm erased (Cat g h gh) c)
    -> (erased (Adj gh x y) r))
  (let-match erased c (CatCons g1 _ gh1 b c1) ((CatNil _) a))
  (AdjThere gh1 b x y (adj-cat-r g1 h gh1 x y a c1)))

(def-fns _ $ (erased spans-cat : (erased (List (Bond)) k g h gh) (subterm erased (Cat g h gh) c) (erased (Spans k g) sg) (erased (Spans k h) sh)
    -> (erased (Spans k gh) r))
  (let-match erased c (CatCons g1 _ gh1 b c1) ((CatNil _) sh))
  (let-match erased sg (SpansCons _ _ x y cx sg1))
  (SpansCons k gh1 x y cx (spans-cat k g1 h gh1 c1 sg1 sh)))

(def-fns _ $ (erased spans-sub-cat : (erased (List (Bond)) k g h gh) (subterm erased (Cat g h gh) c) (erased (Spans k gh) sp)
    -> (erased (Spans k g) sg) (erased (Spans k h) sh))
  (let-match erased c (CatCons g1 _ gh1 b c1) ((CatNil _) (values (SpansNil k) sp)))
  (let-match erased sp (SpansCons _ _ x y cx sp1))
  (let ((erased sg1) (erased sh1)) (spans-sub-cat k g1 h gh1 c1 sp1))
  (values (SpansCons k g1 x y cx sg1) sh1))

(def-fns _ $ (erased conn-lift-l : (erased (List (Bond)) g h gh) (erased (Nat) x y) (subterm erased (Conn g x y) cn) (erased (Cat g h gh) c)
    -> (erased (Conn gh x y) r))
  (let-match erased cn (ConnStep _ _ w _ a c1) ((ConnHere _ _) (ConnHere gh x)))
  (ConnStep gh x w y (adj-cat-l g h gh x w a c) (conn-lift-l g h gh w y c1 c)))

(def-fns _ $ (erased conn-lift-r : (erased (List (Bond)) g h gh) (erased (Nat) x y) (subterm erased (Conn h x y) cn) (erased (Cat g h gh) c)
    -> (erased (Conn gh x y) r))
  (let-match erased cn (ConnStep _ _ w _ a c1) ((ConnHere _ _) (ConnHere gh x)))
  (ConnStep gh x w y (adj-cat-r g h gh x w a c) (conn-lift-r g h gh w y c1 c)))

(def-fns _ $ (erased below-cat : (erased (List (Bond)) g h gh) (erased (Nat) d) (subterm erased (Cat g h gh) c) (erased (Below g d) bg)
    (erased (Below h d) bh) -> (erased (Below gh d) r))
  (let-match erased c (CatCons g1 _ gh1 b c1) ((CatNil _) bh))
  (let-match erased bg (BelowCons _ x y _ lx ly bg1))
  (BelowCons gh1 x y d lx ly (below-cat g1 h gh1 d c1 bg1 bh)))

(def-fns _ $ (erased cat-exists : (subterm erased (List (Bond)) g) (erased (List (Bond)) h) -> (erased (List (Bond)) gh) (erased (Cat g h gh) c))
  (let-match erased g (Cons _ b g1) ((Nil _) (values h (CatNil h))))
  (let ((erased gh1) (erased c1)) (cat-exists g1 h))
  (values (Cons _ b gh1) (CatCons g1 h gh1 b c1)))

(def-fns _ $ (erased graph-below : (erased (Nat) d) (erased (List (Nat)) p q) (erased (List (Bond)) g) (subterm erased (Fun p g) f)
    (erased (Perm d p q) pm) -> (erased (Below g d) r))
  (let-match erased f (FunCons _ g1 x y px f1) ((FunNil _) (BelowNil d)))
  (let-match erased pm (MkPerm _ _ _ ids io lp qp pq))
  (BelowCons g1 x y d (nth-lt-length _ p x d y px lp) (perm-val d x y p q pm px) (graph-below d p q g1 f1 pm)))

; Each node link x-(n x) is the face link back from the edge image of n x.
(def-fns _ $ (erased spans-node : (erased (Nat) d) (erased (List (Nat)) e n f ids en) (erased (List (Bond)) gn ge gf gef)
    (subterm erased (Fun n gn) fn) (erased (Iota d ids) io) (erased (Respects e n en) cen) (erased (Respects f en ids) kn)
    (erased (Graph d e ge) pe) (erased (Graph d f gf) pf) (erased (Cat ge gf gef) c) -> (erased (Spans gef gn) r))
  (let-match erased fn (FunCons _ g1 x y px f1) ((FunNil _) (SpansNil gef)))
  (let ((erased lx)) (nth-lt-length _ n x d y px (respects-length-inv e n en d cen (respects-length-inv f en ids d kn (iota-length d ids io)))))
  (let ((erased w) (erased pw)) (nth-exists _ en d x (respects-length-inv f en ids d kn (iota-length d ids io)) lx))
  (let ((erased ew)) (respects-nth e n en x y w cen px pw))
  (let ((erased fw)) (respects-nth f en ids x w x kn pw (iota-nth d x ids io lx)))
  (SpansCons gef g1 x y
    (conn-sym gef y x (ConnStep gef y w x (adj-cat-l ge gf gef y w (graph-adj d y w e ge pe ew) c)
      (conn-adj gef w x (adj-cat-r ge gf gef w x (graph-adj d w x f gf pf fw) c))))
    (spans-node d e n f ids en g1 ge gf gef f1 io cen kn pe pf c)))

(def-fns _ $ (erased spans-lift-l : (erased (List (Bond)) h r g k) (subterm erased (Spans h k) sp) (erased (Cat h r g) c) -> (erased (Spans g k) res))
  (let-match erased sp (SpansCons _ k1 x y cx sp1) ((SpansNil _) (SpansNil g)))
  (SpansCons g k1 x y (conn-lift-l h r g x y cx c) (spans-lift-l h r g k1 sp1 c)))

(def-fns _ $ (erased spans-lift-r : (erased (List (Bond)) h r g k) (subterm erased (Spans r k) sp) (erased (Cat h r g) c) -> (erased (Spans g k) res))
  (let-match erased sp (SpansCons _ k1 x y cx sp1) ((SpansNil _) (SpansNil g)))
  (SpansCons g k1 x y (conn-lift-r h r g x y cx c) (spans-lift-r h r g k1 sp1 c)))

(def-fns _ $ (erased zip-fn : (erased (List (Nat)) xs ys) (erased (List (Bond)) g h) (subterm erased (Zip xs ys g) z) (erased (Zip xs ys h) w)
    -> (erased (Eq (List (Bond)) g h) e))
  (let-match erased z (ZipCons xs1 ys1 g1 x y z1) ((ZipNil) (let-match erased w (ZipNil)) (Refl _ g)))
  (let-match erased w (ZipCons _ _ h1 _ _ w1))
  (let-match erased (zip-fn xs1 ys1 g1 h1 z1 w1) (Refl _ _))
  (Refl _ g))

(def-fns _ $ (erased graph-fn : (erased (Nat) d) (erased (List (Nat)) p) (erased (List (Bond)) g h) (erased (Graph d p g) gr) (erased (Graph d p h) hr)
    -> (erased (Eq (List (Bond)) g h) e))
  (let-match erased gr (MkGraph _ _ ids _ io lp z))
  (let-match erased hr (MkGraph _ _ ids2 _ io2 lp2 w))
  (let-match erased (iota-fn d ids ids2 io io2) (Refl _ _))
  (zip-fn ids p g h z w))

; The glink components are those of the edge and face links alone.
(def-fns _ $ (erased glink-ef : (erased (Nat) d k) (erased (List (Nat)) e n f) (erased (List (Bond)) ge gf gef g) (erased (Hypermap d e n f) h)
    (erased (Graph d e ge) pe) (erased (Graph d f gf) pf) (erased (Cat ge gf gef) c) (erased (Glink d e n f g) gl)
    (erased (Classes gef d k) cs) -> (erased (Classes g d k) r))
  (let-match erased gl (MkGlink _ _ _ _ ge2 gn gf2 gnf _ pe2 pn pf2 c1 c2))
  (let-match erased (graph-fn d e ge ge2 pe pe2) (Refl _ _))
  (let-match erased (graph-fn d f gf gf2 pf pf2) (Refl _ _))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (let ((erased nfe) (erased pme)) (hyper-perm d e n f h))
  (let ((erased nfn) (erased pmn)) (hyper-perm d n f e (hyper-rot d e n f h)))
  (let ((erased nfp) (erased pmf)) (hyper-perm d f e n (hyper-rot d n f e (hyper-rot d e n f h))))
  (classes-equiv gef g d k cs
    (spans-cat g ge gf gef c (spans-lift-l ge gnf g ge (spans-self ge) c2)
      (spans-lift-r ge gnf g gf (spans-lift-r gn gf gnf gf (spans-self gf) c1) c2))
    (spans-cat gef ge gnf g c2 (spans-lift-l ge gf gef ge (spans-self ge) c)
      (spans-cat gef gn gf gnf c1 (spans-node d e n f ids en gn ge gf gef (graph-fun d n gn pn) io cen kn pe pf c)
        (spans-lift-r ge gf gef gf (spans-self gf) c)))
    (below-cat ge gnf g d c2 (graph-below d e nfe ge (graph-fun d e ge pe) pme)
      (below-cat gn gf gnf d c1 (graph-below d n nfn gn (graph-fun d n gn pn) pmn) (graph-below d f nfp gf (graph-fun d f gf pf) pmf)))))
