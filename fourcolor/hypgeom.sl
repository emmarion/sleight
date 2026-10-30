; The Jordan property of hypermap.v and the special maps and face paths of geometry.v.

; A path of clinks from x through the darts p to y: each step goes from node y' to y', or from x' to face x'.
(def-adts $ (CPath : ((List (Nat)) n f) ((Nat) x) ((List (Nat)) p) ((Nat) y) -> Type)
  enum
  (many CPNil : (erased (List (Nat)) n f) (erased (Nat) x) -> (CPath n f x (Nil (Nat)) x))
  (many CPNode : (erased (List (Nat)) n f p) (erased (Nat) x y z) (erased (Nth (Nat) n y x) pn) (erased (CPath n f y p z) rest)
      -> (CPath n f x (Cons (Nat) y p) z))
  (many CPFace : (erased (List (Nat)) n f p) (erased (Nat) x y z) (erased (Nth (Nat) f x y) pf) (erased (CPath n f y p z) rest)
      -> (CPath n f x (Cons (Nat) y p) z)))

; a occurs in p, and b at or after it.
(def-adts $ (Mem2 : ((List (Nat)) p) ((Nat) a b) -> Type)
  enum
  (many M2Here : (erased (List (Nat)) p) (erased (Nat) a b) (erased (In b (Cons (Nat) a p)) pb) -> (Mem2 (Cons (Nat) a p) a b))
  (many M2There : (erased (List (Nat)) p) (erased (Nat) a b c) (erased (Mem2 p a b) rest) -> (Mem2 (Cons (Nat) c p) a b)))

; x :: p is a Moebius path: duplicate-free, a clink path to y, with the node preimage of y and then node x on p.
(def-adts $ (Moebius : ((List (Nat)) n f) ((Nat) x) ((List (Nat)) p) -> Type)
  enum
  (many MkMoebius : (erased (List (Nat)) n f p) (erased (Nat) x y u v) (erased (Distinct (Cons (Nat) x p)) dp) (erased (CPath n f x p y) cp)
      (erased (Nth (Nat) n u y) pu) (erased (Nth (Nat) n x v) pv) (erased (Mem2 p u v) m) -> (Moebius n f x p)))

; No Moebius path.
(def-adts $ (Jordan : ((List (Nat)) n f) -> Type)
  enum
  (many MkJordan : (erased (List (Nat)) n f) (erased (Level) L)
      (erased (Fn L (erased (Nat) x) (erased (List (Nat)) p) (erased (Moebius n f x p) m) -> (erased (False) r)) thm) -> (Jordan n f)))

; The glink graph has one class.
(def-adts $ (Connected : ((Nat) d) ((List (Nat)) e n f) -> Type)
  enum
  (many MkConnected : (erased (Nat) d) (erased (List (Nat)) e n f) (erased (List (Bond)) g) (erased (Glink d e n f g) gl)
      (erased (Classes g d (Succ (Zero))) cs) -> (Connected d e n f)))

; The cycle of p through x has k darts: from p x, x is reached without leaving x on the way.
(def-adts $ (Order : ((List (Nat)) p) ((Nat) x k) -> Type)
  enum
  (many MkOrder : (erased (List (Nat)) p xs) (erased (Nat) x y k) (erased (Nth (Nat) p x y) px) (erased (Path p (Cons (Nat) x (Nil (Nat))) y x xs) w)
      (erased (Length (Nat) xs k) l) -> (Order p x (Succ k))))

; ks lists the orders of the darts xs.
(def-adts $ (Orders : ((List (Nat)) p xs ks) -> Type)
  enum
  (many OrdNil : (erased (List (Nat)) p) -> (Orders p (Nil (Nat)) (Nil (Nat))))
  (many OrdCons : (erased (List (Nat)) p xs ks) (erased (Nat) x k) (erased (Order p x k) o) (erased (Orders p xs ks) rest)
      -> (Orders p (Cons (Nat) x xs) (Cons (Nat) k ks))))

; ks lists the orders of p at the darts 0..d-1 (for the face permutation, Gonthier's arity).
(def-adts $ (OrderList : ((Nat) d) ((List (Nat)) p ks) -> Type)
  enum
  (many MkOrderList : (erased (Nat) d) (erased (List (Nat)) p ids ks) (erased (Iota d ids) io) (erased (Orders p ids ks) os) -> (OrderList d p ks)))

; Every dart has order c under p (plain for c = 2 and the edge permutation, cubic for c = 3 and the node one).
(def-adts $ (AllOrder : ((Nat) d) ((List (Nat)) p) ((Nat) c) -> Type)
  enum
  (many MkAllOrder : (erased (Nat) d c) (erased (List (Nat)) p ks) (erased (OrderList d p ks) ol) (erased (Repeat (Nat) d c ks) rk)
      -> (AllOrder d p c)))

; Every dart has order at most 3 under n.
(def-adts $ (Precubic : ((Nat) d) ((List (Nat)) n) -> Type)
  enum
  (many MkPrecubic : (erased (Nat) d) (erased (List (Nat)) n ks) (erased (OrderList d n ks) ol) (erased (Under ks (Succ (Succ (Succ (Succ (Zero)))))) u)
      -> (Precubic d n)))

; Every entry of ks is above b.
(def-adts $ (Above : ((List (Nat)) ks) ((Nat) b) -> Type)
  enum
  (many AboveNil : (erased (Nat) b) -> (Above (Nil (Nat)) b))
  (many AboveCons : (erased (List (Nat)) ks) (erased (Nat) k b) (erased (Lt b k) p) (erased (Above ks b) rest) -> (Above (Cons (Nat) k ks) b)))

; Every face has more than four darts.
(def-adts $ (Pentagonal : ((Nat) d) ((List (Nat)) f) -> Type)
  enum
  (many MkPentagonal : (erased (Nat) d) (erased (List (Nat)) f ks) (erased (OrderList d f ks) ol)
      (erased (Above ks (Succ (Succ (Succ (Succ (Zero)))))) a) -> (Pentagonal d f)))

; No dart is on the node cycle of its edge image.
(def-adts $ (Loopfree : ((Nat) d) ((List (Nat)) e n) -> Type)
  enum
  (many MkLoopfree : (erased (Nat) d) (erased (List (Nat)) e n) (erased (List (Bond)) ge gn)
      (erased (Graph d e ge) pe) (erased (Graph d n gn) pn) (erased (AllSep gn ge) s) -> (Loopfree d e n)))

; The darts of p lie on distinct faces: a labelling constant along f gives them distinct labels.
(def-adts $ (Simple : ((List (Nat)) f p) -> Type)
  enum
  (many MkSimple : (erased (List (Nat)) f p lab ls) (erased (Respects lab f lab) rf) (erased (Respects lab p ls) rp) (erased (Distinct ls) dl)
      -> (Simple f p)))

; x then the darts p, each the image of the one before under r, ending at y (Gonthier's fpath).
(def-adts $ (FPath : ((List (Nat)) r) ((Nat) x) ((List (Nat)) p) ((Nat) y) -> Type)
  enum
  (many FPNil : (erased (List (Nat)) r) (erased (Nat) x) -> (FPath r x (Nil (Nat)) x))
  (many FPCons : (erased (List (Nat)) r p) (erased (Nat) x z y) (erased (Nth (Nat) r x z) px) (erased (FPath r z p y) rest)
      -> (FPath r x (Cons (Nat) z p) y)))

; x :: p is a cycle of r on distinct faces of f (Gonthier's sfcycle r).
(def-adts $ (SCycle : ((List (Nat)) r f) ((Nat) x) ((List (Nat)) p) -> Type)
  enum
  (many MkSCycle : (erased (List (Nat)) r f p) (erased (Nat) x y) (erased (FPath r x p y) fp) (erased (Nth (Nat) r y x) back)
      (erased (Simple f (Cons (Nat) x p)) s) -> (SCycle r f x p)))

; x is on the face of a dart of p (Gonthier's fband).
(def-adts $ (Fband : ((List (Nat)) f p) ((Nat) x) -> Type)
  enum
  (many MkFband : (erased (List (Nat)) f p) (erased (Nat) x y) (erased (In y p) py) (erased (SomePath f (Nil (Nat)) x y) w) -> (Fband f p x)))

; x is on no face of a dart of p (Gonthier's kernel): a labelling constant along f tells it from them.
(def-adts $ (Kernel : ((List (Nat)) f p) ((Nat) x) -> Type)
  enum
  (many MkKernel : (erased (List (Nat)) f p lab ls) (erased (Nat) x l) (erased (Respects lab f lab) rf) (erased (Respects lab p ls) rp)
      (erased (Nth (Nat) lab x l) px) (erased (NotIn l ls) out) -> (Kernel f p x)))

(def-fns _ $ (erased order-two : (erased (List (Nat)) p) (erased (Nat) x y) (erased (Order p x (Succ (Succ (Zero)))) o) (erased (Nth (Nat) p x y) px)
    -> (erased (Nth (Nat) p y x) r) (erased (Apart (Nat) Lt y x) ne))
  (let-match erased o (MkOrder _ xs _ y2 _ py2 w l))
  (let-match erased (nth-fn _ p x y y2 px py2) (Refl _ _))
  (let-match erased l (LengthCons _ _ _ _ l1))
  (let-match erased l1 (LengthNil _))
  (let-match erased w (PathStep _ _ _ _ z _ pz out w1))
  (let-match erased w1 (PathHere _ _ _))
  (let-match erased out (NotInCons _ _ _ ne _))
  (values pz ne))

; The order at position j of an order list.
(def-fns _ $ (erased orders-nth : (erased (List (Nat)) p xs ks) (erased (Nat) j x k) (subterm erased (Orders p xs ks) os) (erased (Nth (Nat) xs j x) px)
    (erased (Nth (Nat) ks j k) pk) -> (erased (Order p x k) r))
  (let-match erased os (OrdCons _ xs1 ks1 x0 k0 o os1) (absurd (OrdNil _) px))
  (let-match erased px (NthThere _ _ _ j1 _ px1) ((NthHere _ _ _) (let-match erased pk (NthHere _ _ _)) o))
  (let-match erased pk (NthThere _ _ _ _ _ pk1))
  (orders-nth p xs1 ks1 j1 x k os1 px1 pk1))

; In a map where every dart has order c under p, so does x.
(def-fns _ $ (erased all-order : (erased (Nat) d c x) (erased (List (Nat)) p) (erased (AllOrder d p c) ao) (erased (Lt x d) lx) -> (erased (Order p x c) r))
  (let-match erased ao (MkAllOrder _ _ _ ks ol rk))
  (let-match erased ol (MkOrderList _ _ ids _ io os))
  (orders-nth p ids ks x x c os (iota-nth d x ids io lx) (repeat-nth _ d x c ks rk lx)))

; In a plain map the edge permutation is an involution without fixed points (plain_eq, plain_neq).
(def-fns _ $ (erased plain-eq : (erased (Nat) d x y) (erased (List (Nat)) e) (erased (AllOrder d e (Succ (Succ (Zero)))) pl) (erased (Lt x d) lx)
    (erased (Nth (Nat) e x y) px) -> (erased (Nth (Nat) e y x) r) (erased (Apart (Nat) Lt y x) ne))
  (order-two e x y (all-order d (Succ (Succ (Zero))) x e pl lx) px))

(def-fns _ $ (erased const-adj : (erased (List (Nat)) lab) (erased (List (Bond)) g) (erased (Nat) x y) (subterm erased (Adj g x y) a) (erased (Const lab g) cl)
    -> (erased (Nat) l) (erased (Nth (Nat) lab x l) px) (erased (Nth (Nat) lab y l) py))
  (match erased a _
    ((AdjFwd _ _ _) (let-match erased cl (ConstCons _ _ _ _ l px py _)) (values l px py))
    ((AdjBwd _ _ _) (let-match erased cl (ConstCons _ _ _ _ l px py _)) (values l py px))
    ((AdjThere g1 _ _ _ a1) (let-match erased cl (ConstCons _ _ _ _ _ _ _ cl1)) (const-adj lab g1 x y a1 cl1))))

; A labelling constant along p is constant along its inverse q.
(def-fns _ $ (erased const-inv : (erased (Nat) d) (erased (List (Nat)) lab p q) (erased (List (Bond)) gp gq) (subterm erased (Fun q gq) fq)
    (erased (Perm d q p) pm) (erased (Graph d p gp) gr) (erased (Const lab gp) cl) -> (erased (Const lab gq) r))
  (let-match erased fq (FunCons _ g1 x y py f1) ((FunNil _) (ConstNil lab)))
  (let ((erased l) (erased pl) (erased ql)) (const-adj lab gp y x (graph-adj d y x p gp gr (perm-inv d x y q p pm py)) cl))
  (ConstCons lab g1 x y l ql pl (const-inv d lab p q gp g1 f1 pm gr cl)))

(def-fns _ $ (erased sep-inv : (erased (Nat) d x y) (erased (List (Nat)) p q) (erased (List (Bond)) gp gq) (erased (Sep gp x y) s)
    (erased (Perm d q p) pm) (erased (Graph d p gp) grp) (erased (Graph d q gq) grq) -> (erased (Sep gq x y) r))
  (let-match erased s (MkSep _ _ _ lab l1 l2 cl p1 p2 ne))
  (MkSep gq x y lab l1 l2 (const-inv d lab p q gp gq (graph-fun d q gq grq) pm grp cl) p1 p2 ne))

(def-fns _ $ (erased allsep-dual : (erased (Nat) d) (erased (List (Nat)) e ei n ni) (erased (List (Bond)) ge gei gn gni) (subterm erased (Fun ei gei) fe)
    (erased (Perm d e ei) pe) (erased (Perm d n ni) pn) (erased (Graph d e ge) gre) (erased (Graph d n gn) grn) (erased (Graph d ni gni) grni)
    (erased (AllSep gn ge) sp) -> (erased (AllSep gni gei) r))
  (let-match erased fe (FunCons _ g1 x y py f1) ((FunNil _) (AllSepNil gni)))
  (AllSepCons gni g1 x y
    (sep-inv d x y n ni gn gni (sep-sym gn y x (allsep-adj gn ge y x (graph-adj d y x e ge gre (perm-inv d x y ei e (perm-sym d e ei pe) py)) sp))
      (perm-sym d n ni pn) grn grni)
    (allsep-dual d e ei n ni ge g1 gn gni f1 pe pn gre grn grni sp)))

; A loopless map has a bridgeless dual (one direction of bridgeless_dual).
(def-fns _ $ (erased loopfree-dual : (erased (Nat) d) (erased (List (Nat)) e n f ei fi ni) (erased (Loopfree d e n) lf)
    (erased (Perm d e ei) pe) (erased (Perm d n ni) pn) -> (erased (Bridgeless d ei fi ni) r))
  (let-match erased lf (MkLoopfree _ _ _ ge gn gre grn sp))
  (let ((erased gei) (erased grei)) (perm-graph d ei e (perm-sym d e ei pe)))
  (let ((erased gni) (erased grni)) (perm-graph d ni n (perm-sym d n ni pn)))
  (MkBridgeless d ei fi ni gei gni grei grni (allsep-dual d e ei n ni ge gei gn gni (graph-fun d ei gei grei) pe pn gre grn grni sp)))

(def-fns _ $ (erased allsep-mirror : (erased (Nat) d) (erased (List (Nat)) e n f fi fn) (erased (List (Bond)) ge gf gfi gfn) (subterm erased (Fun fn gfn) ff)
    (erased (Hypermap d e n f) h) (erased (Respects f n fn) rfn) (erased (Perm d f fi) pf) (erased (Graph d e ge) gre) (erased (Graph d f gf) grf)
    (erased (Graph d fi gfi) grfi) (erased (AllSep gf ge) sp) -> (erased (AllSep gfi gfn) r))
  (let-match erased ff (FunCons _ g1 x z pz f1) ((FunNil _) (AllSepNil gfi)))
  (let-match erased h (MkHypermap _ _ _ _ ids fe en nf io cfe ke cen kn cnf kf))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased lx)) (nth-lt-length _ fn x d z pz (respects-length f n fn d rfn ln)))
  (let ((erased y) (erased py)) (nth-exists _ n d x ln lx))
  (let ((erased w) (erased pw)) (nth-exists _ en d x (respects-length e n en d cen ln) lx))
  (let ((erased pyw)) (respects-nth e n en x y w cen py pw))
  (let ((erased pwx)) (respects-nth f en ids x w x kn pw (iota-nth d x ids io lx)))
  (let ((erased s1)) (allsep-adj gf ge y w (graph-adj d y w e ge gre pyw) sp))
  (let ((erased s2)) (sep-move gf w y x (sep-sym gf y w s1) (conn-adj gf w x (graph-adj d w x f gf grf pwx))))
  (let ((erased s3)) (sep-move gf y x z (sep-sym gf x y s2) (conn-adj gf y z (graph-adj d y z f gf grf (respects-nth f n fn x y z rfn py pz)))))
  (AllSepCons gfi g1 x z (sep-inv d x z f fi gf gfi (sep-sym gf z x s3) (perm-sym d f fi pf) grf grfi)
    (allsep-mirror d e n f fi fn ge gf gfi g1 f1 h rfn pf gre grf grfi sp)))

; The mirror of a bridgeless map is bridgeless (one direction of bridgeless_mirror).
(def-fns _ $ (erased bridgeless-mirror : (erased (Nat) d) (erased (List (Nat)) e n f fn ni fi) (erased (Hypermap d e n f) h) (erased (Bridgeless d e n f) b)
    (erased (Respects f n fn) rfn) (erased (Perm d f fi) pf) -> (erased (Bridgeless d fn ni fi) r))
  (let-match erased b (MkBridgeless _ _ _ _ ge gf gre grf sp))
  (let ((erased le) (erased ln) (erased lf)) (hyper-lengths d e n f h))
  (let ((erased gfn) (erased grfn)) (graph-exists d fn (respects-length f n fn d rfn ln)))
  (let ((erased gfi) (erased grfi)) (perm-graph d fi f (perm-sym d f fi pf)))
  (MkBridgeless d fn ni fi gfn gfi grfn grfi (allsep-mirror d e n f fi fn ge gf gfi gfn (graph-fun d fn gfn grfn) h rfn pf gre grf grfi sp)))

(def-fns _ $ (erased order-three : (erased (List (Nat)) p) (erased (Nat) x y) (erased (Order p x (Succ (Succ (Succ (Zero))))) o) (erased (Nth (Nat) p x y) px)
    -> (erased (Nat) z) (erased (Nth (Nat) p y z) py) (erased (Nth (Nat) p z x) pz) (erased (Apart (Nat) Lt y x) ny) (erased (Apart (Nat) Lt z x) nz))
  (let-match erased o (MkOrder _ xs _ y2 _ py2 w l))
  (let-match erased (nth-fn _ p x y y2 px py2) (Refl _ _))
  (let-match erased l (LengthCons _ _ _ _ l1))
  (let-match erased l1 (LengthCons _ _ _ _ l2))
  (let-match erased l2 (LengthNil _))
  (let-match erased w (PathStep _ _ _ _ z _ py out w1))
  (let-match erased w1 (PathStep _ _ _ _ x3 _ pz out2 w2))
  (let-match erased w2 (PathHere _ _ _))
  (let-match erased out (NotInCons _ _ _ ny _))
  (let-match erased out2 (NotInCons _ _ _ nz _))
  (values z py pz ny nz))

; In a cubic map n (n (n x)) = x and n x differs from x (cubic_eq, cubic_neq).
(def-fns _ $ (erased cubic-eq : (erased (Nat) d x y) (erased (List (Nat)) n) (erased (AllOrder d n (Succ (Succ (Succ (Zero))))) cu) (erased (Lt x d) lx)
    (erased (Nth (Nat) n x y) px) -> (erased (Nat) z) (erased (Nth (Nat) n y z) py) (erased (Nth (Nat) n z x) pz) (erased (Apart (Nat) Lt y x) ny)
    (erased (Apart (Nat) Lt z x) nz))
  (order-three n x y (all-order d (Succ (Succ (Succ (Zero)))) x n cu lx) px))
