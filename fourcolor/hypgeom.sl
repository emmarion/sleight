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
