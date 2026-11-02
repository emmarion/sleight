; Entry i of us is n.
(def-adts $ (Ent : ((List Cnt) us) ((Nat) i) ((Nat) n) -> Type)
  enum
  (many MkEnt : (erased (List Cnt) us) (erased (Nat) i n) (erased (Lt n u62-modulus) nb) (erased (Nth Cnt us i (MkCopy (U62) (MkU62 n nb))) x)
      -> (Ent us i n)))

; vs is us with entry i set to n.
(def-adts $ (Upd : ((List Cnt) us) ((Nat) i) ((Nat) n) ((List Cnt) vs) -> Type)
  enum
  (many MkUpd : (erased (List Cnt) us vs) (erased (Nat) i n) (erased (Lt n u62-modulus) nb)
      (erased (SetNth Cnt us i (MkCopy (U62) (MkU62 n nb)) vs) s) -> (Upd us i n vs)))

(def-fns _ $ (erased ent-fn : (erased (List Cnt) us) (erased (Nat) i n m) (erased (Ent us i n) a) (erased (Ent us i m) b) -> (erased (Eq (Nat) n m) e))
  (let-match erased a (MkEnt _ _ _ na x))
  (let-match erased b (MkEnt _ _ _ mb y))
  (let-match erased (nth-fn _ us i _ _ x y) (Refl _ _))
  (Refl _ n))

(def-fns _ $ (erased upd-ent : (erased (List Cnt) us vs) (erased (Nat) i n) (erased (Upd us i n vs) u) -> (erased (Ent vs i n) e))
  (let-match erased u (MkUpd _ _ _ _ nb s))
  (MkEnt vs i n nb (setnth-nth _ us i _ vs s)))

(def-fns _ $ (erased upd-other : (erased (List Cnt) us vs) (erased (Nat) j n i m) (erased (Upd us j n vs) u) (erased (Apart (Nat) Lt j i) ap)
    (erased (Ent us i m) e) -> (erased (Ent vs i m) r))
  (let-match erased u (MkUpd _ _ _ _ nb s))
  (let-match erased e (MkEnt _ _ _ mb x))
  (MkEnt vs i m mb
    (match erased ap _
      ((ApLt _ _ _ _ l) (setnth-nth-gt _ us j i _ _ vs s x l))
      ((ApGt _ _ _ _ l) (setnth-nth-lt _ us j i _ _ vs s x l)))))

(def-fns _ $ (erased upd-len : (erased (List Cnt) us vs) (erased (Nat) i n len) (erased (Upd us i n vs) u) (erased (Length Cnt us len) l)
    -> (erased (Length Cnt vs len) r))
  (let-match erased u (MkUpd _ _ _ _ nb s))
  (setnth-length _ us i len _ vs s l))

(def-fns _ $ (many put-cnt : (erased (List Cnt) us) (unique (Array Cnt us) a) (erased (Nat) len) (erased (Length Cnt us len) l) (many (Nat) i) (erased (Lt i len) il)
    (many (Nat) v) (erased (Lt v u62-modulus) vb) ->
    (erased (List Cnt) us2) (unique (Array Cnt us2) a2 at a) (erased (Upd us i v us2) u) (erased (Length Cnt us2 len) l2))
  (let ((erased old) (erased x)) (nth-exists _ us len i l il))
  (let ((unique y)) (MkCopy (U62) (MkU62 v vb)))
  (let ((erased us2) (unique a2) (erased s)) (array-place-imm _ us a i y old x (imm-cnt old) (imm-cnt y)))
  (let ((erased u)) (MkUpd us us2 i v vb s))
  (values us2 a2 u (upd-len us us2 i v len u l)))

; Entry i of the flag array us is n.
(def-adts $ (Fent : ((List (U8)) us) ((Nat) i) ((Nat) n) -> Type)
  enum
  (many MkFent : (erased (List (U8)) us) (erased (Nat) i n) (erased (Lt n u8-modulus) nb) (erased (Nth (U8) us i (MkU8 n nb)) x) -> (Fent us i n)))

; vs is the flag array us with entry i set to n.
(def-adts $ (Fupd : ((List (U8)) us) ((Nat) i) ((Nat) n) ((List (U8)) vs) -> Type)
  enum
  (many MkFupd : (erased (List (U8)) us vs) (erased (Nat) i n) (erased (Lt n u8-modulus) nb) (erased (SetNth (U8) us i (MkU8 n nb) vs) s) -> (Fupd us i n vs)))

(def-fns _ $ (erased fent-fn : (erased (List (U8)) us) (erased (Nat) i n m) (erased (Fent us i n) a) (erased (Fent us i m) b) -> (erased (Eq (Nat) n m) e))
  (let-match erased a (MkFent _ _ _ na x))
  (let-match erased b (MkFent _ _ _ mb y))
  (let-match erased (nth-fn _ us i _ _ x y) (Refl _ _))
  (Refl _ n))

(def-fns _ $ (erased fupd-ent : (erased (List (U8)) us vs) (erased (Nat) i n) (erased (Fupd us i n vs) u) -> (erased (Fent vs i n) e))
  (let-match erased u (MkFupd _ _ _ _ nb s))
  (MkFent vs i n nb (setnth-nth _ us i _ vs s)))

(def-fns _ $ (erased fupd-other : (erased (List (U8)) us vs) (erased (Nat) j n i m) (erased (Fupd us j n vs) u) (erased (Apart (Nat) Lt j i) ap)
    (erased (Fent us i m) e) -> (erased (Fent vs i m) r))
  (let-match erased u (MkFupd _ _ _ _ nb s))
  (let-match erased e (MkFent _ _ _ mb x))
  (MkFent vs i m mb
    (match erased ap _
      ((ApLt _ _ _ _ l) (setnth-nth-gt _ us j i _ _ vs s x l))
      ((ApGt _ _ _ _ l) (setnth-nth-lt _ us j i _ _ vs s x l)))))

(def-fns _ $ (erased fupd-len : (erased (List (U8)) us vs) (erased (Nat) i n len) (erased (Fupd us i n vs) u) (erased (Length (U8) us len) l)
    -> (erased (Length (U8) vs len) r))
  (let-match erased u (MkFupd _ _ _ _ nb s))
  (setnth-length _ us i len _ vs s l))

(def-fns _ $ (many put-fl : (erased (List (U8)) us) (unique (Bytes us) a) (erased (Nat) len) (erased (Length (U8) us len) l) (many (Nat) i) (erased (Lt i len) il)
    (many (Nat) v) (erased (Lt v u8-modulus) vb) ->
    (erased (List (U8)) us2) (unique (Bytes us2) a2 at a) (erased (Fupd us i v us2) u) (erased (Length (U8) us2 len) l2))
  (let ((erased old) (erased x)) (nth-exists _ us len i l il))
  (let ((erased us2) (unique a2) (erased s)) (bytes-set us a i (MkU8 v vb) old x))
  (let ((erased u)) (MkFupd us us2 i v vb s))
  (values us2 a2 u (fupd-len us us2 i v len u l)))

(def-fns _ $ (many fent-at : (erased (List (U8)) us) (unique (Bytes us) a) (many (Nat) i) (erased (Nat) v) (erased (Fent us i v) x) ->
    (unique a is a2 at a) (many v is k))
  (let-match erased x (MkFent _ _ _ vb y))
  (let ((many c) (unique a2)) (bytes-get _ a i _ y))
  (let-match many c (MkU8 k _))
  (values a2 k))

; The static chromogram tree of one ring size: SxN a node with the children of the four symbols, SxO the slot of a symbol below a leaf,
; SxX an absent subtree; the number in each is its entry in the membership arrays.
(def-adts $ (Sx : -> Type)
  enum
  (many SxN : (many (Nat) i) (many (Sx) t0 t1 t2 t3) -> (Sx))
  (many SxO : (many (Nat) i) -> (Sx))
  (many SxX : -> (Sx)))

; The entries of sx are in [lo, hi): its own first, then its subtrees' in order.
(def-adts $ (Span : ((Sx) sx) ((Nat) lo) ((Nat) hi) -> Type)
  enum
  (many SpX : (erased (Nat) lo) -> (Span (SxX) lo lo))
  (many SpO : (erased (Nat) i) -> (Span (SxO i) i (Succ i)))
  (many SpN : (erased (Nat) i h1 h2 h3 h4) (erased (Sx) t0 t1 t2 t3) (erased (Span t0 (Succ i) h1) s0) (erased (Span t1 h1 h2) s1)
      (erased (Span t2 h2 h3) s2) (erased (Span t3 h3 h4) s3) -> (Span (SxN i t0 t1 t2 t3) i h4)))

; gs is the set whose selections by the four symbols are a0 to a3, at a node whose children have depth j.
(def-adts $ (GTop : ((Nat) j) ((GSet) a0) ((GSet) a1) ((GSet) a2) ((GSet) a3) ((GSet) gs) -> Type)
  enum
  (many GTN : (erased (Nat) j) (erased (Gtree) g0 g1 g2 g3) -> (GTop (Succ j) (GSG g0) (GSG g1) (GSG g2) (GSG g3) (GSG (GNode g0 g1 g2 g3))))
  (many GTL : (erased (Gtree) g) (erased (Bool) b0 b1 b2 b3) (erased (GSet) a0 a1 a2 a3) (erased (LeafSet g (MkBits b0 b1 b2 b3)) l)
      (erased (BSet b0 a0) q0) (erased (BSet b1 a1) q1) (erased (BSet b2 a2) q2) (erased (BSet b3 a3) q3) -> (GTop (Zero) a0 a1 a2 a3 (GSG g))))

; Over the static tree sx of depth j, the entries of us hold gs: 0 for an empty set, 1 otherwise.
(def-adts $ (Gm : ((List (U8)) us) ((Nat) j) ((Sx) sx) ((GSet) gs) -> Type)
  enum
  (many GmX : (erased (List (U8)) us) (erased (Nat) j) -> (Gm us j (SxX) (GSG (GEmpty))))
  (many GmO0 : (erased (List (U8)) us) (erased (Nat) i) (erased (Fent us i (Zero)) x) -> (Gm us (Zero) (SxO i) (GSG (GEmpty))))
  (many GmO1 : (erased (List (U8)) us) (erased (Nat) i) (erased (Fent us i (Succ (Zero))) x) -> (Gm us (Zero) (SxO i) (GSOne)))
  (many GmN0 : (erased (List (U8)) us) (erased (Nat) j i) (erased (Sx) t0 t1 t2 t3) (erased (Fent us i (Zero)) x)
      -> (Gm us (Succ j) (SxN i t0 t1 t2 t3) (GSG (GEmpty))))
  (many GmN1 : (erased (List (U8)) us) (erased (Nat) j i) (erased (Sx) t0 t1 t2 t3) (erased (GSet) a0 a1 a2 a3 gs) (erased (Fent us i (Succ (Zero))) x)
      (erased (Gm us j t0 a0) m0) (erased (Gm us j t1 a1) m1) (erased (Gm us j t2 a2) m2) (erased (Gm us j t3 a3) m3) (erased (GTop j a0 a1 a2 a3 gs) tp)
      -> (Gm us (Succ j) (SxN i t0 t1 t2 t3) gs)))

; k is outside [lo, hi).
(def-adts $ (Out : ((Nat) k) ((Nat) lo) ((Nat) hi) -> Type)
  enum
  (many OutL : (erased (Nat) k lo hi) (erased (Lt k lo) l) -> (Out k lo hi))
  (many OutR : (erased (Nat) k lo hi) (erased (Lt hi (Succ k)) l) -> (Out k lo hi)))

; [a, b) and [lo, hi) do not meet.
(def-adts $ (Dis : ((Nat) a) ((Nat) b) ((Nat) lo) ((Nat) hi) -> Type)
  enum
  (many DisL : (erased (Nat) a b lo hi) (erased (Lt b (Succ lo)) p) -> (Dis a b lo hi))
  (many DisR : (erased (Nat) a b lo hi) (erased (Lt hi (Succ a)) p) -> (Dis a b lo hi)))

; vs is us with entries set only in [lo, hi).
(def-adts $ (Wr : ((List (U8)) us) ((List (U8)) vs) ((Nat) lo) ((Nat) hi) -> Type)
  enum
  (many WrN : (erased (List (U8)) us) (erased (Nat) lo hi) -> (Wr us us lo hi))
  (many WrS : (erased (List (U8)) us ws vs) (erased (Nat) lo hi k v) (erased (Wr us ws lo hi) w) (erased (Fupd ws k v vs) u)
      (erased (Lt lo (Succ k)) p) (erased (Lt k hi) q) -> (Wr us vs lo hi)))

(def-fns _ $ (erased span-le : (erased (Sx) sx) (erased (Nat) lo hi) (subterm erased (Span sx lo hi) sp) -> (erased (Lt lo (Succ hi)) r))
  (match erased sp _
    ((SpX _) (lt-succ lo))
    ((SpO _) (lt-weaken _ _ (lt-succ lo)))
    ((SpN _ h1 h2 h3 _ t0 t1 t2 t3 s0 s1 s2 s3)
      (le-trans _ _ _ (lt-weaken _ _ (lt-pred _ _ (span-le t0 (Succ lo) h1 s0)))
        (le-trans _ _ _ (span-le t1 h1 h2 s1) (le-trans _ _ _ (span-le t2 h2 h3 s2) (span-le t3 h3 hi s3)))))))

; The own entry i of a node and its children's spans' bounds, in order.
(def-fns _ $ (erased span-n : (erased (Nat) i h1 h2 h3 h4) (erased (Sx) t0 t1 t2 t3) (erased (Span t0 (Succ i) h1) s0) (erased (Span t1 h1 h2) s1)
    (erased (Span t2 h2 h3) s2) (erased (Span t3 h3 h4) s3) -> (erased (Lt i h1) a1) (erased (Lt i h2) a2) (erased (Lt i h3) a3) (erased (Lt i h4) a4))
  (let ((erased a1)) (lt-pred _ _ (span-le t0 (Succ i) h1 s0)))
  (let ((erased a2)) (lt-le-trans _ _ _ a1 (span-le t1 h1 h2 s1)))
  (let ((erased a3)) (lt-le-trans _ _ _ a2 (span-le t2 h2 h3 s2)))
  (values a1 a2 a3 (lt-le-trans _ _ _ a3 (span-le t3 h3 h4 s3))))

(def-fns _ $ (erased out-apart : (erased (Nat) k lo hi) (erased (Out k lo hi) o) (erased (Lt lo hi) l) -> (erased (Apart (Nat) Lt k lo) r))
  (match erased o _
    ((OutL _ _ _ a) (ApLt (Nat) Lt k lo a))
    ((OutR _ _ _ b) (ApGt (Nat) Lt k lo (lt-le-trans lo hi k l b)))))

(def-fns _ $ (erased out-sub : (erased (Nat) k lo hi lo2 hi2) (erased (Out k lo hi) o) (erased (Lt lo (Succ lo2)) p) (erased (Lt hi2 (Succ hi)) q)
    -> (erased (Out k lo2 hi2) r))
  (match erased o _
    ((OutL _ _ _ a) (OutL k lo2 hi2 (lt-le-trans k lo lo2 a p)))
    ((OutR _ _ _ b) (OutR k lo2 hi2 (le-trans hi2 hi k q b)))))

(def-fns _ $ (erased dis-out : (erased (Nat) a b lo hi k) (erased (Dis a b lo hi) d) (erased (Lt lo (Succ k)) p) (erased (Lt k hi) q) -> (erased (Out k a b) r))
  (match erased d _
    ((DisL _ _ _ _ x) (OutR k a b (le-trans b lo k x p)))
    ((DisR _ _ _ _ x) (OutL k a b (lt-le-trans k hi a q x)))))

(def-fns _ $ (erased gm-upd : (erased (List (U8)) us vs) (erased (Nat) j k v lo hi) (erased (Sx) sx) (erased (GSet) gs) (subterm erased (Gm us j sx gs) m)
    (erased (Span sx lo hi) sp) (erased (Fupd us k v vs) u) (erased (Out k lo hi) o) -> (erased (Gm vs j sx gs) r))
  (match erased m _
    ((GmX _ _) (GmX vs j))
    ((GmO0 _ i x) (let-match erased sp (SpO _)) (GmO0 vs i (fupd-other us vs k v i _ u (out-apart k i hi o (lt-succ i)) x)))
    ((GmO1 _ i x) (let-match erased sp (SpO _)) (GmO1 vs i (fupd-other us vs k v i _ u (out-apart k i hi o (lt-succ i)) x)))
    ((GmN0 _ j1 i t0 t1 t2 t3 x)
      (let-match erased sp (SpN _ h1 h2 h3 _ _ _ _ _ s0 s1 s2 s3))
      (let ((erased _) (erased _) (erased _) (erased a4)) (span-n i h1 h2 h3 hi t0 t1 t2 t3 s0 s1 s2 s3))
      (GmN0 vs j1 i t0 t1 t2 t3 (fupd-other us vs k v i _ u (out-apart k i hi o a4) x)))
    ((GmN1 _ j1 i t0 t1 t2 t3 a0 a1 a2 a3 _ x m0 m1 m2 m3 tp)
      (let-match erased sp (SpN _ h1 h2 h3 _ _ _ _ _ s0 s1 s2 s3))
      (let ((erased b1) (erased b2) (erased b3) (erased a4)) (span-n i h1 h2 h3 hi t0 t1 t2 t3 s0 s1 s2 s3))
      (let ((erased e2) (erased e3)) (values (le-trans _ _ _ (span-le t2 h2 h3 s2) (span-le t3 h3 hi s3)) (span-le t3 h3 hi s3)))
      (let ((erased e1)) (le-trans _ _ _ (span-le t1 h1 h2 s1) e2))
      (GmN1 vs j1 i t0 t1 t2 t3 a0 a1 a2 a3 gs (fupd-other us vs k v i _ u (out-apart k i hi o a4) x)
        (gm-upd us vs j1 k v (Succ i) h1 t0 a0 m0 s0 u (out-sub k i hi (Succ i) h1 o (lt-weaken _ _ (lt-succ i)) e1))
        (gm-upd us vs j1 k v h1 h2 t1 a1 m1 s1 u (out-sub k i hi h1 h2 o (lt-weaken _ _ b1) e2))
        (gm-upd us vs j1 k v h2 h3 t2 a2 m2 s2 u (out-sub k i hi h2 h3 o (lt-weaken _ _ b2) e3))
        (gm-upd us vs j1 k v h3 hi t3 a3 m3 s3 u (out-sub k i hi h3 hi o (lt-weaken _ _ b3) (lt-succ hi)))
        tp))))

(def-fns _ $ (erased gm-wr : (erased (List (U8)) us vs) (erased (Nat) j a b lo hi) (erased (Sx) sx) (erased (GSet) gs) (erased (Gm us j sx gs) m)
    (erased (Span sx a b) sp) (subterm erased (Wr us vs lo hi) w) (erased (Dis a b lo hi) d) -> (erased (Gm vs j sx gs) r))
  (match erased w _
    ((WrN _ _ _) m)
    ((WrS _ ws _ _ _ k v w1 u p q) (gm-upd ws vs j k v a b sx gs (gm-wr us ws j a b lo hi sx gs m sp w1 d) sp u (dis-out a b lo hi k d p q)))))

(def-fns _ $ (erased wr-widen : (erased (List (U8)) us vs) (erased (Nat) lo hi lo2 hi2) (subterm erased (Wr us vs lo hi) w) (erased (Lt lo2 (Succ lo)) a)
    (erased (Lt hi (Succ hi2)) b) -> (erased (Wr us vs lo2 hi2) r))
  (match erased w _
    ((WrN _ _ _) (WrN us lo2 hi2))
    ((WrS _ ws _ _ _ k v w1 u p q) (WrS us ws vs lo2 hi2 k v (wr-widen us ws lo hi lo2 hi2 w1 a b) u (le-trans _ _ _ a p) (lt-le-trans _ _ _ q b)))))

(def-fns _ $ (erased wr-join : (erased (List (U8)) us ws vs) (erased (Nat) lo hi) (erased (Wr us ws lo hi) w1) (subterm erased (Wr ws vs lo hi) w2)
    -> (erased (Wr us vs lo hi) r))
  (match erased w2 _
    ((WrN _ _ _) w1)
    ((WrS _ xs _ _ _ k v w3 u p q) (WrS us xs vs lo hi k v (wr-join us ws xs lo hi w1 w3) u p q))))

(def-fns _ $ (erased wr-app : (erased (List (U8)) us ws vs) (erased (Nat) lo mid hi) (erased (Wr us ws lo mid) w1) (erased (Wr ws vs mid hi) w2)
    (erased (Lt lo (Succ mid)) a) (erased (Lt mid (Succ hi)) b) -> (erased (Wr us vs lo hi) r))
  (wr-join us ws vs lo hi (wr-widen us ws lo mid lo hi w1 (lt-succ lo) b) (wr-widen ws vs mid hi lo hi w2 a (lt-succ hi))))

(def-fns _ $ (erased gm-ent-n : (erased (List (U8)) us) (erased (Nat) j i) (erased (Sx) t0 t1 t2 t3) (erased (GSet) gs) (erased (Gm us j (SxN i t0 t1 t2 t3) gs) m)
    -> (erased (Nat) v) (erased (Fent us i v) x))
  (match erased m _ ((GmN0 _ _ _ _ _ _ _ x) (values (Zero) x)) ((GmN1 _ _ _ _ _ _ _ _ _ _ _ _ x _ _ _ _ _) (values (Succ (Zero)) x))))

(def-fns _ $ (erased gm-ent-o : (erased (List (U8)) us) (erased (Nat) j i) (erased (GSet) gs) (erased (Gm us j (SxO i) gs) m) -> (erased (Nat) v) (erased (Fent us i v) x))
  (match erased m _ ((GmO0 _ _ x) (values (Zero) x)) ((GmO1 _ _ x) (values (Succ (Zero)) x))))

(def-fns _ $ (erased gm-zero-n : (erased (List (U8)) us) (erased (Nat) j i) (erased (Sx) t0 t1 t2 t3) (erased (GSet) gs) (erased (Gm us j (SxN i t0 t1 t2 t3) gs) m)
    (erased (Fent us i (Zero)) x) -> (erased (Eq (GSet) gs (GSG (GEmpty))) r))
  (let-match erased m (GmN0 _ _ _ _ _ _ _ _) (absurd (GmN1 _ _ _ _ _ _ _ _ _ _ _ _ y _ _ _ _ _) (fent-fn us i _ _ x y)))
  (Refl _ gs))

(def-fns _ $ (erased gm-one-n : (erased (List (U8)) us) (erased (Nat) j i v) (erased (Sx) t0 t1 t2 t3) (erased (GSet) gs)
    (erased (Gm us (Succ j) (SxN i t0 t1 t2 t3) gs) m) (erased (Fent us i (Succ v)) x) ->
    (erased (GSet) a0 a1 a2 a3) (erased (Gm us j t0 a0) m0) (erased (Gm us j t1 a1) m1) (erased (Gm us j t2 a2) m2) (erased (Gm us j t3 a3) m3)
    (erased (GTop j a0 a1 a2 a3 gs) tp))
  (let-match erased m (GmN1 _ _ _ _ _ _ _ a0 a1 a2 a3 _ _ m0 m1 m2 m3 tp) (absurd (GmN0 _ _ _ _ _ _ _ y) (fent-fn us i _ _ y x)))
  (values a0 a1 a2 a3 m0 m1 m2 m3 tp))

(def-fns _ $ (erased gm-zero-o : (erased (List (U8)) us) (erased (Nat) j i) (erased (GSet) gs) (erased (Gm us j (SxO i) gs) m) (erased (Fent us i (Zero)) x)
    -> (erased (Eq (GSet) gs (GSG (GEmpty))) r))
  (let-match erased m (GmO0 _ _ _) (absurd (GmO1 _ _ y) (fent-fn us i _ _ x y)))
  (Refl _ gs))

(def-fns _ $ (erased gm-one-o : (erased (List (U8)) us) (erased (Nat) j i v) (erased (GSet) gs) (erased (Gm us j (SxO i) gs) m) (erased (Fent us i (Succ v)) x)
    -> (erased (Eq (GSet) gs (GSOne)) r))
  (let-match erased m (GmO1 _ _ _) (absurd (GmO0 _ _ y) (fent-fn us i _ _ y x)))
  (Refl _ gs))

(def-fns _ $ (many ent-at : (erased (List Cnt) us) (unique (Array Cnt us) a) (many (Nat) i) (erased (Nat) v) (erased (Ent us i v) x) ->
    (unique a is a2 at a) (many v is k))
  (let-match erased x (MkEnt _ _ _ vb y))
  (let ((many c) (unique a2)) (array-get _ _ a i _ y))
  (let-match many c (MkU62 k _))
  (values a2 k))

; sx is absent or a node whose entry in us is not 0.
(def-adts $ (SxLive : ((List (U8)) us) ((Sx) sx) -> Type)
  enum
  (many LiX : (erased (List (U8)) us) -> (SxLive us (SxX)))
  (many LiN : (erased (List (U8)) us) (erased (Nat) i v) (erased (Sx) t0 t1 t2 t3) (erased (Fent us i (Succ v)) x) -> (SxLive us (SxN i t0 t1 t2 t3))))

(def-adts $ (LvC : ((List (U8)) us) ((Sx) sx) ((GSet) gs) -> Type)
  enum
  (many LcDead : (erased (List (U8)) us) (erased (Sx) sx) -> (LvC us sx (GSG (GEmpty))))
  (many LcLive : (erased (List (U8)) us) (erased (Sx) sx) (erased (GSet) gs) (erased (SxLive us sx) l) -> (LvC us sx gs)))

(def-fns _ $ (many live-c : (erased (List (U8)) us) (unique (Bytes us) a) (erased (Nat) j) (many (Sx) x) (erased (GSet) gs) (erased (Gm us (Succ j) x gs) m) ->
    (unique a is a2 at a) (many (LvC us x gs) c))
  (let-match many x (SxN i c0 c1 c2 c3)
    ((SxX) (let-match erased m (GmX _ _)) (values a (LcDead us x)))
    (absurd (SxO _) m))
  (let ((erased v) (erased xe)) (gm-ent-n us (Succ j) i c0 c1 c2 c3 gs m))
  (let ((unique a2) (many k)) (fent-at us a i v xe))
  (let-match many k (Succ k1) ((Zero) (let-match erased (gm-zero-n us (Succ j) i c0 c1 c2 c3 gs m xe) (Refl _ _)) (values a2 (LcDead us x))))
  (values a2 (LcLive us x gs (LiN us i k1 c0 c1 c2 c3 xe))))

(def-fns _ $ (erased monus-one : (erased (Nat) a k m m2) (erased (Monus a k m) p) (erased (Monus m (Succ (Zero)) m2) q) -> (erased (Monus a (Succ k) m2) r))
  (monus-add a k m (Succ (Zero)) m2 (Succ k) p q (add-succ-right k (Zero) k (add-zero-right k))))

(def-fns _ $ (erased monus-uniq : (erased (Nat) a k m m2) (subterm erased (Monus a k m) p) (erased (Monus a k m2) q) -> (erased (Eq (Nat) m m2) e))
  (match erased p _
    ((MoZ _) (let-match erased q (MoZ _)) (Refl _ m))
    ((MoE _) (let-match erased q (MoE _)) (Refl _ m))
    ((MoS a1 k1 _ p1) (let-match erased q (MoS _ _ _ q1)) (monus-uniq a1 k1 m m2 p1 q1))))

; After k decrements from (n0, 0), an entry and its gone entry are (n, x): x is n0 once a decrement has reached a live entry.
(def-adts $ (Ds : ((Nat) n0) ((Nat) k) ((Nat) n) ((Nat) x) -> Type)
  enum
  (many DsU : (erased (Nat) n0) -> (Ds n0 (Zero) n0 (Zero)))
  (many DsT : (erased (Nat) n1 k1 n) (erased (Monus (Succ n1) (Succ k1) n) o) -> (Ds (Succ n1) (Succ k1) n (Succ n1)))
  (many DsE : (erased (Nat) k) -> (Ds (Zero) k (Zero) (Zero))))

; One decrement: (n, x) becomes (n2, x2).
(def-adts $ (Dk : ((Nat) n) ((Nat) x) ((Nat) n2) ((Nat) x2) -> Type)
  enum
  (many DkZ : (erased (Nat) x) -> (Dk (Zero) x (Zero) x))
  (many DkF : (erased (Nat) n1) -> (Dk (Succ n1) (Zero) n1 (Succ n1)))
  (many DkS : (erased (Nat) n1 x1) -> (Dk (Succ n1) (Succ x1) n1 (Succ x1))))

(def-fns _ $ (erased ds-dk : (erased (Nat) n0 k n x n2 x2) (erased (Ds n0 k n x) s) (erased (Dk n x n2 x2) d) -> (erased (Ds n0 (Succ k) n2 x2) r))
  (match erased d _
    ((DkZ _)
      (match erased s _
        ((DsU _) (DsE (Succ (Zero))))
        ((DsT n1 k1 _ o) (DsT n1 (Succ k1) (Zero) (monus-one (Succ n1) (Succ k1) (Zero) (Zero) o (MoE (Zero)))))
        ((DsE _) (DsE (Succ k)))))
    ((DkF n1) (let-match erased s (DsU _)) (DsT n1 (Zero) n1 (MoS n1 (Zero) n1 (MoZ n1))))
    ((DkS n1 x1)
      (let-match erased s (DsT m1 k1 _ o))
      (DsT m1 (Succ k1) n1 (monus-one (Succ m1) (Succ k1) (Succ n1) n1 o (MoS n1 (Zero) n1 (MoZ n1)))))))

(def-adts $ (HasT : ((Nat) x) ((List (Nat)) T) ((Nat) i) -> Type)
  enum
  (many HtZ : (erased (List (Nat)) T) (erased (Nat) i) -> (HasT (Zero) T i))
  (many HtE : (erased (Nat) x i) (erased (List (Nat)) T) (erased (Elem (Nat) i T) e) -> (HasT x T i)))

(def-fns _ $ (erased has-cons : (erased (Nat) x i j) (erased (List (Nat)) T) (erased (HasT x T i) h) -> (erased (HasT x (Cons (Nat) j T) i) r))
  (match erased h _
    ((HtZ _ _) (HtZ (Cons _ j T) i))
    ((HtE _ _ _ e) (HtE x i (Cons _ j T) (ElThere _ i j T e)))))

; The walk's state: counts, gone entries, and the indices whose gone entry it set.
(def-adts $ (Sv : -> Type)
  enum
  (many MkSv : (many (List Cnt) us ws) (many (List (Nat)) T) -> (Sv)))

; Trace index i of s started from count n0 and has had k decrements.
(def-adts $ (TrS : ((Sv) s) ((Nat) i) ((Nat) n0) ((Nat) k) -> Type)
  enum
  (many MkTrS : (erased (List Cnt) us ws) (erased (List (Nat)) T) (erased (Nat) i n0 k n x) (erased (Ent us i n) eu) (erased (Ent ws i x) ew)
      (erased (Ds n0 k n x) st) (erased (HasT x T i) ht) -> (TrS (MkSv us ws T) i n0 k)))

; One decrement of index i.
(def-adts $ (Tick : ((Nat) i) ((Sv) s) ((Sv) s2) -> Type)
  enum
  (many TkZ : (erased (Nat) i) (erased (List Cnt) us ws) (erased (List (Nat)) T) (erased (Ent us i (Zero)) e)
      -> (Tick i (MkSv us ws T) (MkSv us ws T)))
  (many TkF : (erased (Nat) i n1) (erased (List Cnt) us ws us2 ws2) (erased (List (Nat)) T) (erased (Ent us i (Succ n1)) e) (erased (Ent ws i (Zero)) f)
      (erased (Upd us i n1 us2) u) (erased (Upd ws i (Succ n1) ws2) w) -> (Tick i (MkSv us ws T) (MkSv us2 ws2 (Cons (Nat) i T))))
  (many TkS : (erased (Nat) i n1 x1) (erased (List Cnt) us ws us2) (erased (List (Nat)) T) (erased (Ent us i (Succ n1)) e) (erased (Ent ws i (Succ x1)) f)
      (erased (Upd us i n1 us2) u) -> (Tick i (MkSv us ws T) (MkSv us2 ws T))))

(def-fns _ $ (erased tick-same : (erased (Nat) i n0 k) (erased (Sv) s s2) (erased (Tick i s s2) tk) (erased (TrS s i n0 k) tr) -> (erased (TrS s2 i n0 (Succ k)) r))
  (let-match erased tr (MkTrS us ws T _ _ _ n x eu ew st ht))
  (match erased tk _
    ((TkZ _ _ _ _ e)
      (let-match erased (ent-fn us i n (Zero) eu e) (Refl _ _))
      (MkTrS us ws T i n0 (Succ k) n x eu ew (ds-dk n0 k n x n x st (DkZ x)) ht))
    ((TkF _ n1 _ _ us2 ws2 _ e f u w)
      (let-match erased (ent-fn us i n (Succ n1) eu e) (Refl _ _))
      (let-match erased (ent-fn ws i x (Zero) ew f) (Refl _ _))
      (MkTrS us2 ws2 (Cons _ i T) i n0 (Succ k) n1 (Succ n1) (upd-ent us us2 i n1 u) (upd-ent ws ws2 i (Succ n1) w)
        (ds-dk n0 k n x n1 (Succ n1) st (DkF n1)) (HtE (Succ n1) i (Cons _ i T) (ElHere _ i T))))
    ((TkS _ n1 x1 _ _ us2 _ e f u)
      (let-match erased (ent-fn us i n (Succ n1) eu e) (Refl _ _))
      (let-match erased (ent-fn ws i x (Succ x1) ew f) (Refl _ _))
      (MkTrS us2 ws T i n0 (Succ k) n1 x (upd-ent us us2 i n1 u) ew (ds-dk n0 k n x n1 x st (DkS n1 x1)) ht))))

(def-fns _ $ (erased tick-other : (erased (Nat) j i n0 k) (erased (Sv) s s2) (erased (Tick j s s2) tk) (erased (Apart (Nat) Lt j i) ap)
    (erased (TrS s i n0 k) tr) -> (erased (TrS s2 i n0 k) r))
  (let-match erased tr (MkTrS us ws T _ _ _ n x eu ew st ht))
  (match erased tk _
    ((TkZ _ _ _ _ _) tr)
    ((TkF _ n1 _ _ us2 ws2 _ _ _ u w)
      (MkTrS us2 ws2 (Cons _ j T) i n0 k n x (upd-other us us2 j n1 i n u ap eu) (upd-other ws ws2 j (Succ n1) i x w ap ew) st (has-cons x i j T ht)))
    ((TkS _ n1 _ _ _ us2 _ _ _ u) (MkTrS us2 ws T i n0 k n x (upd-other us us2 j n1 i n u ap eu) ew st ht))))

(def-adts $ (ColNe : ((Col) e) ((Col) f) -> Type)
  enum
  (many N12 : -> (ColNe (C1) (C2)))
  (many N13 : -> (ColNe (C1) (C3)))
  (many N21 : -> (ColNe (C2) (C1)))
  (many N23 : -> (ColNe (C2) (C3)))
  (many N31 : -> (ColNe (C3) (C1)))
  (many N32 : -> (ColNe (C3) (C2))))

(def-adts $ (KidCmp : ((Col) e) ((Col) f) ((Nat) a) ((Nat) b) -> Type)
  enum
  (many KcSame : (erased (Col) e) (erased (Nat) a) -> (KidCmp e e a a))
  (many KcNe : (erased (Col) e f) (erased (Nat) a b) (erased (ColNe e f) ne) (erased (Apart (Nat) Lt a b) ap) -> (KidCmp e f a b)))

(def-fns _ $ (erased kid-dec : (erased (Nat) p a b) (erased (Col) e f) (erased (Kid p e a) ka) (erased (Kid p f b) kb) -> (erased (KidCmp e f a b) r))
  (match erased ka _
    ((Ki1 _ q0 t0)
      (match erased kb _
        ((Ki1 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcSame e a))
        ((Ki2 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N12) (ApLt _ _ a b (lt-succ a))))
        ((Ki3 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N13) (ApLt _ _ a b (lt-weaken a (Succ a) (lt-succ a)))))))
    ((Ki2 _ q0 t0)
      (match erased kb _
        ((Ki1 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N21) (ApGt _ _ a b (lt-succ b))))
        ((Ki2 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcSame e a))
        ((Ki3 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N23) (ApLt _ _ a b (lt-succ a))))))
    ((Ki3 _ q0 t0)
      (match erased kb _
        ((Ki1 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N31) (ApGt _ _ a b (lt-weaken b (Succ b) (lt-succ b)))))
        ((Ki2 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcNe e f a b (N32) (ApGt _ _ a b (lt-succ b))))
        ((Ki3 _ q1 t1) (let-match erased (thrice-fn p q0 q1 t0 t1) (Refl _ _)) (KcSame e a))))))

(def-fns _ $ (erased kid-inj : (erased (Nat) a b c) (erased (Col) e f) (erased (Kid a e c) ka) (erased (Kid b f c) kb) ->
    (erased (Eq (Nat) a b) r) (erased (Eq (Col) e f) s))
  (let-match erased (nat-eq a b) (Equal _ _ _) (absurd (Unequal _ _ _ _ ap) (apart-irrefl c (kid-apart a b c c e f ap ka kb))))
  (let-match erased (kid-dec a c c e f ka kb) (KcSame _ _) (absurd (KcNe _ _ _ _ _ ap) (apart-irrefl c ap)))
  (values (Refl _ a) (Refl _ e)))

; n is the heap node of the trie path whose colours, last first, are pre.
(def-adts $ (HIdx : ((List (Col)) pre) ((Nat) n) -> Type)
  enum
  (many HxNil : -> (HIdx (Nil (Col)) (Zero)))
  (many HxCons : (erased (List (Col)) pre) (erased (Nat) n c) (erased (Col) e) (erased (HIdx pre n) hi) (erased (Kid n e c) k)
      -> (HIdx (Cons (Col) e pre) (Succ c))))

(def-fns _ $ (erased hidx-fn : (erased (List (Col)) pre pre2) (erased (Nat) n) (subterm erased (HIdx pre n) a) (erased (HIdx pre2 n) b)
    -> (erased (Eq (List (Col)) pre pre2) r))
  (match erased a _
    ((HxNil) (let-match erased b (HxNil)) (Refl _ pre))
    ((HxCons pre1 n1 c e a1 k1)
      (let-match erased b (HxCons pre3 n3 _ e3 b1 k3))
      (let ((erased q1) (erased q2)) (kid-inj n1 n3 c e e3 k1 k3))
      (let-match erased q1 (Refl _ _))
      (let-match erased q2 (Refl _ _))
      (let-match erased (hidx-fn pre1 pre3 n1 a1 b1) (Refl _ _))
      (Refl _ pre))))

(def-fns _ $ (erased sel0-empty : (erased (Ctree) t v) (erased (CtSel t (C0) v) s) -> (erased (Eq (Ctree) v (CEmpty)) r))
  (match erased s _ ((SelN0 _ _ _) (Refl _ v)) ((SelL _ _) (Refl _ v)) ((SelE _) (Refl _ v))))

(def-fns _ $ (erased ctat-fn : (erased (Ctree) top t u) (erased (List (Col)) pre) (subterm erased (CtAt top pre t) a) (erased (CtAt top pre u) b)
    -> (erased (Eq (Ctree) t u) r))
  (match erased a _
    ((AtNil _) (let-match erased b (AtNil _)) (Refl _ t))
    ((AtCons _ v _ pre1 e a1 s1)
      (let-match erased b (AtCons _ w _ _ _ b1 s2))
      (let-match erased (ctat-fn top v w pre1 a1 b1) (Refl _ _))
      (sel-fn v t u e s1 s2))))

(def-fns _ $ (erased ctat-exists : (erased (Ctree) top) (subterm erased (List (Col)) pre) -> (erased (Ctree) t) (erased (CtAt top pre t) a))
  (let-match erased pre (Cons _ e pre1) ((Nil _) (values top (AtNil top))))
  (let ((erased u) (erased a1)) (ctat-exists top pre1))
  (let ((erased t) (erased s)) (sel-exists u e))
  (values t (AtCons top u t pre1 e a1 s)))

; Each node of t, of height j at the heap node n of ls, holds g unless t is empty there.
(def-adts $ (Lv : ((List (U8)) ls) ((Nat) g) ((Nat) j) ((Nat) n) ((Ctree) t) -> Type)
  enum
  (many LvE : (erased (List (U8)) ls) (erased (Nat) g j n) -> (Lv ls g j n (CEmpty)))
  (many LvL : (erased (List (U8)) ls) (erased (Nat) g n) (erased (Ctree) lf) (erased (Fent ls n g) x) -> (Lv ls g (Zero) n (CLeaf lf)))
  (many LvN : (erased (List (U8)) ls) (erased (Nat) g j n q) (erased (Ctree) t1 t2 t3) (erased (Fent ls n g) x) (erased (Thrice n q) tq)
      (erased (Lv ls g j (Succ q) t1) l1) (erased (Lv ls g j (Succ (Succ q)) t2) l2) (erased (Lv ls g j (Succ (Succ (Succ q))) t3) l3)
      -> (Lv ls g (Succ j) n (CNode t1 t2 t3))))

(def-fns _ $ (erased lv-ne : (erased (List (U8)) ls) (erased (Nat) g j n v) (erased (Ctree) t) (erased (Lv ls g j n t) lv) (erased (Fent ls n v) x)
    (erased (Apart (Nat) Lt v g) ap) -> (erased (Eq (Ctree) t (CEmpty)) r))
  (let-match erased lv (LvE _ _ _ _)
    (absurd (LvL _ _ _ _ y) (let-match erased (fent-fn ls n v g x y) (Refl _ _)) (apart-irrefl g ap))
    (absurd (LvN _ _ _ _ _ _ _ _ y _ _ _ _) (let-match erased (fent-fn ls n v g x y) (Refl _ _)) (apart-irrefl g ap)))
  (Refl _ t))

(def-fns _ $ (erased lv-down : (erased (List (U8)) ls) (erased (Nat) g j n c) (erased (Ctree) t u) (erased (Col) e) (erased (Lv ls g (Succ j) n t) lv)
    (erased (Kid n e c) k) (erased (CtSel t e u) s) -> (erased (Lv ls g j (Succ c) u) r))
  (let-match erased lv (LvN _ _ _ _ q _ _ _ _ tq l1 l2 l3) ((LvE _ _ _ _) (let-match erased s (SelE _)) (LvE ls g j (Succ c))))
  (match erased k _
    ((Ki1 _ _ tk) (let-match erased (thrice-fn n q c tq tk) (Refl _ _)) (let-match erased s (SelN1 _ _ _)) l1)
    ((Ki2 _ c0 tk) (let-match erased (thrice-fn n q c0 tq tk) (Refl _ _)) (let-match erased s (SelN2 _ _ _)) l2)
    ((Ki3 _ c0 tk) (let-match erased (thrice-fn n q c0 tq tk) (Refl _ _)) (let-match erased s (SelN3 _ _ _)) l3)))

(def-fns _ $ (erased kill-ent : (erased (List (U8)) ls ls2) (erased (Nat) g n m v) (erased (Ctree) top t) (erased (List (Col)) pre prem) (erased (Occ t) o)
    (erased (Fent ls n g) x) (erased (HIdx pre n) hi) (erased (CtAt top pre t) pt) (erased (Fupd ls m v ls2) u) (erased (HIdx prem m) hm)
    (erased (CtAt top prem (CEmpty)) am) -> (erased (Fent ls2 n g) r))
  (let-match erased (nat-eq m n) (Unequal _ _ _ _ ap)
    (absurd (Equal _ _ _)
      (let-match erased (hidx-fn pre prem n hi hm) (Refl _ _))
      (let-match erased (ctat-fn top t (CEmpty) pre pt am) (Refl _ _))
      o))
  (fupd-other ls ls2 m v n g u ap x))

(def-fns _ $ (erased lv-kill : (erased (List (U8)) ls ls2) (erased (Nat) g j n m v) (erased (Ctree) top t) (erased (List (Col)) pre prem)
    (subterm erased (Lv ls g j n t) lv) (erased (HIdx pre n) hi) (erased (CtAt top pre t) pt) (erased (Fupd ls m v ls2) u) (erased (HIdx prem m) hm)
    (erased (CtAt top prem (CEmpty)) am) -> (erased (Lv ls2 g j n t) r))
  (let-match erased lv (LvN _ _ j1 _ q t1 t2 t3 x tq l1 l2 l3)
    ((LvE _ _ _ _) (LvE ls2 g j n))
    ((LvL _ _ _ lf x) (LvL ls2 g n lf (kill-ent ls ls2 g n m v top t pre prem (OccL lf) x hi pt u hm am))))
  (let ((erased c1) (erased c2) (erased c3)) (values (Cons _ (C1) pre) (Cons _ (C2) pre) (Cons _ (C3) pre)))
  (LvN ls2 g j1 n q t1 t2 t3 (kill-ent ls ls2 g n m v top t pre prem (OccN t1 t2 t3) x hi pt u hm am) tq
    (lv-kill ls ls2 g j1 (Succ q) m v top t1 c1 prem l1 (HxCons pre n q (C1) hi (Ki1 n q tq)) (AtCons top t t1 pre (C1) pt (SelN1 t1 t2 t3)) u hm am)
    (lv-kill ls ls2 g j1 (Succ (Succ q)) m v top t2 c2 prem l2 (HxCons pre n (Succ q) (C2) hi (Ki2 n q tq)) (AtCons top t t2 pre (C2) pt (SelN2 t1 t2 t3))
      u hm am)
    (lv-kill ls ls2 g j1 (Succ (Succ (Succ q))) m v top t3 c3 prem l3 (HxCons pre n (Succ (Succ q)) (C3) hi (Ki3 n q tq))
      (AtCons top t t3 pre (C3) pt (SelN3 t1 t2 t3)) u hm am)))

(def-fns _ $ (erased add-sh : (erased (Nat) a b c) (erased (Add a (Succ b) c) p) -> (erased (Add (Succ a) b c) q))
  (let ((erased c1) (erased e) (erased q)) (add-succ-right-inv a b c p))
  (let-match erased e (Refl _ _))
  (AddSucc a b c1 q))

(def-fns _ $ (erased lv-at : (erased (List (U8)) ls) (erased (Nat) g j n d H) (erased (Ctree) top t) (subterm erased (List (Col)) pre)
    (erased (Lv ls g H (Zero) top) lv) (erased (HIdx pre n) hi) (erased (CtAt top pre t) pt) (erased (Length (Col) pre d) le) (erased (Add d j H) ad)
    -> (erased (Lv ls g j n t) r))
  (match erased pre _
    ((Nil _) (let-match erased hi (HxNil)) (let-match erased pt (AtNil _)) (let-match erased le (LengthNil _)) (let-match erased ad (AddZero _)) lv)
    ((Cons _ e pre1)
      (let-match erased hi (HxCons _ n1 c _ hi1 k))
      (let-match erased pt (AtCons _ u _ _ _ at1 s))
      (let-match erased le (LengthCons _ _ _ d1 le1))
      (let-match erased ad (AddSucc _ _ Hq ad1))
      (lv-down ls g j n1 c u t e (lv-at ls g (Succ j) n1 d1 H top u pre1 lv hi1 at1 le1 (add-succ-right d1 j Hq ad1)) k s))))

(def-fns _ $ (erased canon-at : (erased (Nat) j d H) (erased (Ctree) top t) (subterm erased (List (Col)) pre) (erased (CtCanon H top) c)
    (erased (CtAt top pre t) pt) (erased (Length (Col) pre d) le) (erased (Add d j H) ad) -> (erased (CtCanon j t) r))
  (match erased pre _
    ((Nil _) (let-match erased pt (AtNil _)) (let-match erased le (LengthNil _)) (let-match erased ad (AddZero _)) c)
    ((Cons _ e pre1)
      (let-match erased pt (AtCons _ u _ _ _ at1 s))
      (let-match erased le (LengthCons _ _ _ d1 le1))
      (let-match erased ad (AddSucc _ _ Hq ad1))
      (let-match erased (canon-at (Succ j) d1 H top u pre1 c at1 le1 (add-succ-right d1 j Hq ad1)) (CanN _ t1 t2 t3 _ c1 c2 c3 cn))
      (let ((erased s1) (erased s2) (erased s3)) (cn-sel t1 t2 t3 u cn))
      (match erased e _
        ((C0) (let-match erased (sel0-empty u t s) (Refl _ _)) (canon-empty j))
        ((C1) (let-match erased (sel-fn u t t1 e s s1) (Refl _ _)) c1)
        ((C2) (let-match erased (sel-fn u t t2 e s s2) (Refl _ _)) c2)
        ((C3) (let-match erased (sel-fn u t t3 e s s3) (Refl _ _)) c3)))))

(def-fns _ $ (erased tfit-kid : (erased (Nat) len j n c) (erased (Col) e) (erased (TrieFit len (Succ j) n) tf) (erased (Kid n e c) k)
    -> (erased (TrieFit len j (Succ c)) r))
  (let-match erased tf (TfN _ _ _ q _ tq f1 f2 f3))
  (match erased k _
    ((Ki1 _ _ tk) (let-match erased (thrice-fn n q c tq tk) (Refl _ _)) f1)
    ((Ki2 _ c0 tk) (let-match erased (thrice-fn n q c0 tq tk) (Refl _ _)) f2)
    ((Ki3 _ c0 tk) (let-match erased (thrice-fn n q c0 tq tk) (Refl _ _)) f3)))

(def-fns _ $ (erased tfit-at : (erased (Nat) len j n d H) (subterm erased (List (Col)) pre) (erased (TrieFit len H (Zero)) tf)
    (erased (HIdx pre n) hi) (erased (Length (Col) pre d) le) (erased (Add d j H) ad) -> (erased (TrieFit len j n) r))
  (match erased pre _
    ((Nil _) (let-match erased hi (HxNil)) (let-match erased le (LengthNil _)) (let-match erased ad (AddZero _)) tf)
    ((Cons _ e pre1)
      (let-match erased hi (HxCons _ n1 c _ hi1 k))
      (let-match erased le (LengthCons _ _ _ d1 le1))
      (let-match erased ad (AddSucc _ _ Hq ad1))
      (tfit-kid len j n1 c e (tfit-at len (Succ j) n1 d1 H pre1 tf hi1 le1 (add-succ-right d1 j Hq ad1)) k))))

(def-fns _ $ (erased mul3-thrice : (erased (Nat) q k) (subterm erased (Mul q (Succ (Succ (Succ (Zero)))) k) mm) -> (erased (Thrice q k) t))
  (let-match erased mm (MulSucc q1 _ k1 _ mm1 ad) ((MulZero _) (TZ)))
  (let ((erased a3))
    (add-succ-right k1 (Succ (Succ (Zero))) (Succ (Succ k1)) (add-succ-right k1 (Succ (Zero)) (Succ k1) (add-succ-right k1 (Zero) k1 (add-zero-right k1)))))
  (let-match erased (add-fn k1 (Succ (Succ (Succ (Zero)))) k (Succ (Succ (Succ k1))) ad a3) (Refl _ _))
  (TS q1 k1 (mul3-thrice q1 k1 mm1)))

(def-fns _ $ (erased kid-div : (erased (Nat) p q c k r) (erased (Col) e) (erased (Kid p e c) kp) (erased (Mul q (Succ (Succ (Succ (Zero)))) k) mm)
    (erased (Add k r c) ad) (erased (Lt r (Succ (Succ (Succ (Zero))))) rl) -> (erased (Eq (Nat) p q) eq))
  (let ((erased tq)) (mul3-thrice q k mm))
  (let ((erased a0)) (add-zero-right k))
  (let ((erased a1)) (add-succ-right k (Zero) k a0))
  (let ((erased a2)) (add-succ-right k (Succ (Zero)) (Succ k) a1))
  (let ((erased f) (erased kq))
    (match erased r (((Col) f) ((Kid q f c) kq))
      ((Zero) (let-match erased (add-fn k (Zero) c k ad a0) (Refl _ _)) (values (C1) (Ki1 q k tq)))
      ((Succ r1)
        (match erased r1 _
          ((Zero) (let-match erased (add-fn k (Succ (Zero)) c (Succ k) ad a1) (Refl _ _)) (values (C2) (Ki2 q k tq)))
          ((Succ r2)
            (let-match erased r2 (Zero)
              (absurd (Succ _) (let-match erased rl (LtS _ _ l1)) (let-match erased l1 (LtS _ _ l2)) (let-match erased l2 (LtS _ _ l3)) l3))
            (let-match erased (add-fn k (Succ (Succ (Zero))) c (Succ (Succ k)) ad a2) (Refl _ _))
            (values (C3) (Ki3 q k tq)))))))
  (let ((erased eq) (erased _)) (kid-inj p q c e f kp kq))
  eq)

(def-fns _ $ (erased node-dead : (erased (List (U8)) ls) (erased (Nat) g j m q v1 v2 v3) (erased (Ctree) u) (erased (Lv ls g (Succ j) m u) lv)
    (erased (CtCanon (Succ j) u) cu) (erased (Thrice m q) tq) (erased (Fent ls (Succ q) v1) x1) (erased (Fent ls (Succ (Succ q)) v2) x2)
    (erased (Fent ls (Succ (Succ (Succ q))) v3) x3) (erased (Apart (Nat) Lt v1 g) a1) (erased (Apart (Nat) Lt v2 g) a2) (erased (Apart (Nat) Lt v3 g) a3)
    -> (erased (Eq (Ctree) u (CEmpty)) r))
  (let-match erased lv (LvN _ _ _ _ q2 t1 t2 t3 _ tq2 l1 l2 l3) ((LvE _ _ _ _) (Refl _ u)))
  (let-match erased (thrice-fn m q q2 tq tq2) (Refl _ _))
  (let-match erased (lv-ne ls g j (Succ q) v1 t1 l1 x1 a1) (Refl _ _))
  (let-match erased (lv-ne ls g j (Succ (Succ q)) v2 t2 l2 x2 a2) (Refl _ _))
  (let-match erased (lv-ne ls g j (Succ (Succ (Succ q))) v3 t3 l3 x3 a3) (Refl _ _))
  (let-match erased cu (CanN _ _ _ _ _ _ _ _ cn))
  (let-match erased cn (CnN _ _ _ o))
  (match erased (occ3-empty o) _))

(let ((many flag-live)) (Succ (Zero)))

(def-fns _ $ (many flag-get : (erased (List (U8)) ls) (unique (Bytes ls) fa) (erased (Nat) len) (erased (Length (U8) ls len) ll) (many (Nat) i)
    (erased (Lt i len) il) (many (Nat) g) (erased (Lt g u8-modulus) gb) -> (unique fa is fa2 at fa) (erased (Nat) v) (erased (Fent ls i v) x)
    (many (EqDec (Nat) Lt v g) r))
  (let ((erased old) (erased y)) (nth-exists _ ls len i ll il))
  (let-match erased old (MkU8 v vb))
  (let ((many w) (unique fa2)) (bytes-get _ fa i old y))
  (let-match many w (MkU8 k _))
  (values fa2 v (MkFent ls i v vb y) (u62-eq k g (lt-trans _ _ _ vb u8-below-u62) (lt-trans _ _ _ gb u8-below-u62))))

(def-fns _ $ (many leaf-tree : (subterm many (Nat) n) -> (many (Ctree) t) (erased (CtRoot t n) r) (erased (CtH (Zero) t) k))
  (let-match many n (Succ n1) ((Zero) (values (CEmpty) (RootE) (HE (Zero)))))
  (let ((many t1) (erased r1) (erased k1)) (notail $ leaf-tree n1))
  (values (CLeaf t1) (RootL t1 n1 r1) (HL t1 k1)))

(def-fns _ $ (many tally-tree : (subterm many (Nat) j) (many (Nat) p n) (erased (List Cnt) us) (many (Array Cnt us) a) (erased (Fit us) f)
    (erased (Ctree) t) (erased (Tally us j p t) b) (erased (List (U8)) ls) (unique (Bytes ls) fa) (erased (Nat) lenL) (erased (Length (U8) ls lenL) ll)
    (erased (Lt lenL u62-modulus) lbl) (erased (TrieFit lenL j n) tf) (erased (Lv ls flag-live j n t) lv) -> (unique fa is fa2 at fa) (many t is r))
  (let ((unique fa1) (erased vf) (erased xf) (many d)) (flag-get ls fa lenL ll n (tfit-lt _ _ _ tf) flag-live flag-one-lt8))
  (let-match many d (Equal _ _ _)
    ((Unequal _ _ _ _ ap) (let-match erased (lv-ne ls flag-live j n vf t lv xf ap) (Refl _ _)) (values fa1 (CEmpty))))
  (match many j _
    ((Zero)
      (let-match erased b (TaL _ _ _ _ _ x rt k))
      (let-match many (array-get-many _ _ a p _ x) (MkCopy _ v))
      (let-match many v (MkU62 m _))
      (let ((many u) (erased ru) (erased ku)) (leaf-tree m))
      (let-match erased (leaf-fn u t m ru ku rt k) (Refl _ _))
      (values fa1 u))
    ((Succ j1)
      (let-match erased b (TaN _ _ _ q t1 t2 t3 _ tq b1 b2 b3 cn))
      (let ((erased q3)) (tally-u62 us j1 (Succ (Succ q)) t3 b3 f))
      (let ((erased q2)) (lt-trans (Succ q) (Succ (Succ q)) u62-modulus (lt-succ (Succ q)) q3))
      (let ((many r1)) (thrice-c p q tq (lt-trans q (Succ q) u62-modulus (lt-succ q) q2)))
      (let ((many r2)) (u62-inc r1 q2))
      (let-match erased tf (TfN _ _ _ qn _ tn f1 f2 f3))
      (let ((many n1) (erased n2-bd) (erased n3-bd)) (node-kids n qn tn (lt-trans _ _ _ (tfit-lt _ _ _ f3) lbl)))
      (let ((many n2)) (u62-inc n1 n2-bd))
      (let ((many n3)) (u62-inc n2 n3-bd))
      (let ((erased s1) (erased s2) (erased s3)) (cn-sel t1 t2 t3 t cn))
      (let ((unique fa2) (many c1))
        (notail $ tally-tree j1 r1 n1 us a f t1 b1 ls fa1 lenL ll lbl f1 (lv-down ls flag-live j1 n qn t t1 (C1) lv (Ki1 n qn tn) s1)))
      (let ((unique fa3) (many c2))
        (notail $ tally-tree j1 r2 n2 us a f t2 b2 ls fa2 lenL ll lbl f2 (lv-down ls flag-live j1 n (Succ qn) t t2 (C2) lv (Ki2 n qn tn) s2)))
      (let ((unique fa4) (many c3))
        (notail $ tally-tree j1 (u62-inc r2 q3) n3 us a f t3 b3 ls fa3 lenL ll lbl f3 (lv-down ls flag-live j1 n (Succ (Succ qn)) t t3 (C3) lv (Ki3 n qn tn) s3)))
      (let ((many r) (erased cr)) (cn-c c1 c2 c3))
      (let-match erased (cn-fn t1 t2 t3 r t cr cn) (Refl _ _))
      (values fa4 r))))

(def-fns _ $ (erased flags-lv : (erased (List (U8)) us) (erased (Nat) j n) (erased (Ctree) t) (subterm erased (Flags us j n t) f) -> (erased (Lv us flag-live j n t) r))
  (match erased f _
    ((FlE _ _ _ _ _) (LvE us flag-live j n))
    ((FlL _ _ lf b x) (LvL us flag-live n lf (MkFent us n flag-live b x)))
    ((FlN _ j1 _ q t1 t2 t3 b x tq f1 f2 f3 _)
      (LvN us flag-live j1 n q t1 t2 t3 (MkFent us n flag-live b x) tq (flags-lv us j1 (Succ q) t1 f1) (flags-lv us j1 (Succ (Succ q)) t2 f2)
        (flags-lv us j1 (Succ (Succ (Succ q))) t3 f3)))))

; The heap node n is that of the prefix p, at the end of the colours pre, last first, d of the H colours in, with j to go; ls has room below it.
(def-adts $ (Nd : ((List (U8)) ls) ((Nat) H) ((Nat) j) ((Nat) p) ((Nat) n) -> Type)
  enum
  (many MkNd : (erased (List (U8)) ls) (erased (Nat) H j p n d len) (erased (List (Col)) pre) (erased (RIdx pre p) ri) (erased (HIdx pre n) hi)
      (erased (Length (Col) pre d) le) (erased (Add d j H) ad) (erased (Length (U8) ls len) ll) (erased (Lt len u62-modulus) lb)
      (erased (TrieFit len j n) tf) -> (Nd ls H j p n)))

; The block of the prefix p in us0, of j more colours, holds t, whose nodes ls flags live from the heap node n.
(def-adts $ (Pz : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) ((Nat) p) ((Nat) n) ((Ctree) t) -> Type)
  enum
  (many MkPz : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n) (erased (Ctree) t) (erased (Tally us0 j p t) tb) (erased (Lv ls flag-live j n t) lv)
      (erased (Nd ls H j p n) nd) -> (Pz us0 ls H j p n t)))

(def-fns _ $ (erased pz-down : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n q c) (erased (Ctree) t) (erased (Col) e)
    (erased (Pz us0 ls H (Succ j) p n t) pz) (erased (Kid p e q) kp) (erased (Kid n e c) kn) ->
    (erased (Ctree) u) (erased (CtSel t e u) s) (erased (Pz us0 ls H j q (Succ c) u) r))
  (let-match erased pz (MkPz _ _ _ _ _ _ _ tb lv nd))
  (let ((erased u) (erased ub) (erased s)) (tally-down us0 j p q t e tb kp))
  (let-match erased nd (MkNd _ _ _ _ _ d len pre ri hi le ad ll lb tf))
  (values u s (MkPz us0 ls H j q (Succ c) u ub (lv-down ls flag-live j n c t u e lv kn s)
    (MkNd ls H j q (Succ c) (Succ d) len (Cons _ e pre) (RICons pre p q e ri kp) (HxCons pre n c e hi kn) (LengthCons _ e pre d le) (add-sh d j H ad) ll lb
      (tfit-kid len j n c e tf kn)))))

; k2 is k, unless the count n0 of the trace is 0.
(def-adts $ (Bump : ((Nat) n0) ((Nat) k) ((Nat) k2) -> Type)
  enum
  (many BmEq : (erased (Nat) n0 k) -> (Bump n0 k k))
  (many BmZ : (erased (Nat) k k2) -> (Bump (Zero) k k2)))

(def-fns _ $ (erased bump-add : (erased (Nat) n0 a c c1 k) (erased (Bump n0 c c1) b) (erased (Add a c k) ad) ->
    (erased (Nat) k1) (erased (Add a c1 k1) ad1) (erased (Bump n0 k k1) b1))
  (let-match erased b (BmZ _ _) ((BmEq _ _) (values k ad (BmEq n0 k))))
  (let ((erased k1) (erased ad1)) (add a c1))
  (values k1 ad1 (BmZ k k1)))

(def-fns _ $ (erased bump-fix : (erased (Sv) s) (erased (Nat) i n0 k c c1 k1) (erased (Bump n0 c c1) b) (erased (Add k c1 k1) ad1)
    (erased (TrS s i n0 k1) tr) -> (erased (Nat) k2) (erased (Add k c k2) ad) (erased (TrS s i n0 k2) tr2))
  (let-match erased b (BmZ _ _) ((BmEq _ _) (values k1 ad1 tr)))
  (let ((erased k2) (erased ad)) (add k c))
  (let-match erased tr (MkTrS us ws T _ _ _ n x eu ew st ht))
  (let-match erased st (DsE _) ((DsU _) (values k2 ad (MkTrS us ws T i n0 k2 n x eu ew (DsE k2) ht))))
  (values k2 ad (MkTrS us ws T i n0 k2 n x eu ew (DsE k2) ht)))

; A trace prefix p at the heap node n, with its bit stack: its block in us0, of j more colours, holds t.
(def-adts $ (Pr : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) -> Type)
  enum
  (many MkPr : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (many (Nat) p n) (many (Bstack) bs) (erased (Ctree) t) (erased (Pz us0 ls H j p n t) pz)
      -> (Pr us0 ls H j)))

; The pairs of P, held at runtime.
(def-adts $ (Ps : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) ((List (Pr us0 ls H j)) P) -> Type)
  enum
  (many PsNil : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) -> (Ps us0 ls H j (Nil (Pr us0 ls H j))))
  (many PsCons : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (many (Nat) p n) (many (Bstack) bs) (erased (Ctree) t) (erased (Pz us0 ls H j p n t) pz)
      (erased (List (Pr us0 ls H j)) P) (many (Ps us0 ls H j P) rest) -> (Ps us0 ls H j (Cons (Pr us0 ls H j) (MkPr us0 ls H j p n bs t pz) P))))

(def-adts $ (IsPop : ((Gsym) s) -> Type)
  enum
  (many IP0 : -> (IsPop (GPop0)))
  (many IP1 : -> (IsPop (GPop1))))

; Q is Q0 after the pairs that x steps to under the symbol s.
(def-adts $ (Ch : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) ((Gsym) s) ((Pr us0 ls H (Succ j)) x) ((List (Pr us0 ls H j)) Q0)
    ((List (Pr us0 ls H j)) Q) -> Type)
  enum
  (many ChSkip : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n q c) (erased (Bstack) bs) (erased (Ctree) t u) (erased (Pz us0 ls H (Succ j) p n t) pz)
      (erased (Pz us0 ls H j q c u) pu) (erased (Kid p (C1) q) k) (erased (List (Pr us0 ls H j)) Q0)
      -> (Ch us0 ls H j (GSkip) (MkPr us0 ls H (Succ j) p n bs t pz) Q0 (Cons (Pr us0 ls H j) (MkPr us0 ls H j q c bs u pu) Q0)))
  (many ChPush : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n q2 q3 c2 c3) (erased (Bstack) bs) (erased (Ctree) t u2 u3)
      (erased (Pz us0 ls H (Succ j) p n t) pz) (erased (Pz us0 ls H j q2 c2 u2) p2) (erased (Pz us0 ls H j q3 c3 u3) p3) (erased (Kid p (C2) q2) k2)
      (erased (Kid p (C3) q3) k3) (erased (List (Pr us0 ls H j)) Q0)
      -> (Ch us0 ls H j (GPush) (MkPr us0 ls H (Succ j) p n bs t pz) Q0
           (Cons (Pr us0 ls H j) (MkPr us0 ls H j q2 c2 (BP0 bs) u2 p2) (Cons (Pr us0 ls H j) (MkPr us0 ls H j q3 c3 (BP1 bs) u3 p3) Q0))))
  (many ChPop : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n q c) (erased (Gsym) s) (erased (Col) e) (erased (Bstack) bs b) (erased (Ctree) t u)
      (erased (Pz us0 ls H (Succ j) p n t) pz) (erased (Pz us0 ls H j q c u) pu) (erased (Popped bs b) pp) (erased (Sym s bs e b) y) (erased (Kid p e q) k)
      (erased (List (Pr us0 ls H j)) Q0)
      -> (Ch us0 ls H j s (MkPr us0 ls H (Succ j) p n bs t pz) Q0 (Cons (Pr us0 ls H j) (MkPr us0 ls H j q c b u pu) Q0)))
  (many ChNone : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n) (erased (Gsym) s) (erased (Ctree) t) (erased (IsPop s) ip)
      (erased (Pz us0 ls H (Succ j) p n t) pz) (erased (List (Pr us0 ls H j)) Q0) -> (Ch us0 ls H j s (MkPr us0 ls H (Succ j) p n (BS0) t pz) Q0 Q0)))

; Q holds the pairs that those of P step to under s.
(def-adts $ (Stp : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) ((Gsym) s) ((List (Pr us0 ls H (Succ j))) P) ((List (Pr us0 ls H j)) Q) -> Type)
  enum
  (many StpNil : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (erased (Gsym) s) -> (Stp us0 ls H j s (Nil (Pr us0 ls H (Succ j))) (Nil (Pr us0 ls H j))))
  (many StpCons : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (erased (Gsym) s) (erased (Pr us0 ls H (Succ j)) x) (erased (List (Pr us0 ls H (Succ j))) P)
      (erased (List (Pr us0 ls H j)) Q0 Q) (erased (Stp us0 ls H j s P Q0) st) (erased (Ch us0 ls H j s x Q0 Q) ch)
      -> (Stp us0 ls H j s (Cons (Pr us0 ls H (Succ j)) x P) Q)))

; No chromogram symbol s matches the colour e from the stack bs.
(def-adts $ (NoSym : ((Gsym) s) ((Bstack) bs) ((Col) e) -> Type)
  enum
  (many NsSk2 : (erased (Bstack) bs) -> (NoSym (GSkip) bs (C2)))
  (many NsSk3 : (erased (Bstack) bs) -> (NoSym (GSkip) bs (C3)))
  (many NsPu1 : (erased (Bstack) bs) -> (NoSym (GPush) bs (C1)))
  (many NsP01 : (erased (Bstack) bs) -> (NoSym (GPop0) bs (C1)))
  (many NsP11 : (erased (Bstack) bs) -> (NoSym (GPop1) bs (C1)))
  (many NsP0E : (erased (Col) e) -> (NoSym (GPop0) (BS0) e))
  (many NsP1E : (erased (Col) e) -> (NoSym (GPop1) (BS0) e))
  (many NsP03 : (erased (Bstack) b) -> (NoSym (GPop0) (BP0 b) (C3)))
  (many NsP02 : (erased (Bstack) b) -> (NoSym (GPop0) (BP1 b) (C2)))
  (many NsP12 : (erased (Bstack) b) -> (NoSym (GPop1) (BP0 b) (C2)))
  (many NsP13 : (erased (Bstack) b) -> (NoSym (GPop1) (BP1 b) (C3))))

(def-fns _ $ (erased absurd nosym-sym : (erased (Gsym) s) (erased (Bstack) bs b) (erased (Col) e) (erased (NoSym s bs e) ns) (erased (Sym s bs e b) y)
    -> (erased (False) f))
  (match erased y _
    (absurd (SSkip _) ns) (absurd (SPush2 _) ns) (absurd (SPush3 _) ns) (absurd (SPop02 _) ns)
    (absurd (SPop12 _) ns) (absurd (SPop03 _) ns) (absurd (SPop13 _) ns)))

(def-fns _ $ (erased pop-nosym : (erased (Gsym) s) (erased (Bstack) bs b) (erased (Col) e2 e) (erased (Popped bs b) pp) (erased (Sym s bs e2 b) y)
    (erased (ColNe e2 e) ne) -> (erased (NoSym s bs e) r))
  (match erased y _
    (absurd (SSkip _) pp) (absurd (SPush2 _) pp) (absurd (SPush3 _) pp)
    ((SPop02 _) (match erased ne _ ((N21) (NsP01 bs)) ((N23) (NsP03 b))))
    ((SPop12 _) (match erased ne _ ((N21) (NsP11 bs)) ((N23) (NsP13 b))))
    ((SPop03 _) (match erased ne _ ((N31) (NsP01 bs)) ((N32) (NsP02 b))))
    ((SPop13 _) (match erased ne _ ((N31) (NsP11 bs)) ((N32) (NsP12 b))))))

; c counts the chromograms of gs matching rest from the stack that s leaves after matching e from bs, or is 0 when s cannot.
(def-adts $ (SymC : ((Gsym) s) ((Bstack) bs) ((Col) e) ((GSet) gs) ((List (Col)) rest) ((Nat) c) -> Type)
  enum
  (many ScY : (erased (Gsym) s) (erased (Bstack) bs bs2) (erased (Col) e) (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) c)
      (erased (Sym s bs e bs2) y) (erased (MC gs bs2 rest c) m) -> (SymC s bs e gs rest c))
  (many ScN : (erased (Gsym) s) (erased (Bstack) bs) (erased (Col) e) (erased (GSet) gs) (erased (List (Col)) rest) (erased (NoSym s bs e) ns)
      -> (SymC s bs e gs rest (Zero))))

(def-fns _ $ (erased symc-none : (erased (Gsym) s) (erased (Bstack) bs) (erased (Col) e) (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) c)
    (erased (SymC s bs e gs rest c) sc) (erased (NoSym s bs e) ns) -> (erased (Eq (Nat) c (Zero)) r))
  (let-match erased sc (ScN _ _ _ _ _ _) (absurd (ScY _ _ b _ _ _ _ y _) (nosym-sym s bs b e ns y)))
  (Refl _ c))

(def-fns _ $ (erased symc-some : (erased (Gsym) s) (erased (Bstack) bs b) (erased (Col) e) (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) c)
    (erased (SymC s bs e gs rest c) sc) (erased (Sym s bs e b) y) -> (erased (MC gs b rest c) r))
  (let-match erased sc (ScY _ _ b2 _ _ _ _ y2 m) (absurd (ScN _ _ _ _ _ ns) (nosym-sym s bs b e ns y)))
  (let-match erased (sym-fn s bs b2 b e y2 y) (Refl _ _))
  m)

(def-adts $ (Sum4 : ((Nat) c0) ((Nat) c1) ((Nat) c2) ((Nat) c3) ((Nat) n) -> Type)
  enum
  (many MkSum4 : (erased (Nat) c0 c1 c2 c3 n x y) (erased (Add c0 c1 x) a1) (erased (Add x c2 y) a2) (erased (Add y c3 n) a3) -> (Sum4 c0 c1 c2 c3 n)))

(def-fns _ $ (erased sum4-pp : (erased (Nat) a b) -> (erased (Nat) n) (erased (Add a b n) ad) (erased (Sum4 a (Zero) b (Zero) n) s2)
    (erased (Sum4 a (Zero) (Zero) b n) s3))
  (let ((erased n) (erased ad)) (add a b))
  (values n ad (MkSum4 a (Zero) b (Zero) n a n (add-zero-right a) ad (add-zero-right n)) (MkSum4 a (Zero) (Zero) b n a a (add-zero-right a) (add-zero-right a) ad)))

; k counts, over the pairs of P at the prefix q, the chromograms of gs that match rest from their stacks.
(def-adts $ (PairCnt : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) ((List (Pr us0 ls H j)) P) ((GSet) gs) ((Nat) q) ((List (Col)) rest) ((Nat) k)
    -> Type)
  enum
  (many PaNil : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j q) (erased (GSet) gs) (erased (List (Col)) rest)
      -> (PairCnt us0 ls H j (Nil (Pr us0 ls H j)) gs q rest (Zero)))
  (many PaHit : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j q n) (erased (Bstack) bs) (erased (Ctree) t) (erased (Pz us0 ls H j q n t) pz)
      (erased (List (Pr us0 ls H j)) P) (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) a c k) (erased (MC gs bs rest a) m)
      (erased (PairCnt us0 ls H j P gs q rest c) pc) (erased (Add a c k) ad)
      -> (PairCnt us0 ls H j (Cons (Pr us0 ls H j) (MkPr us0 ls H j q n bs t pz) P) gs q rest k))
  (many PaMiss : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n q) (erased (Bstack) bs) (erased (Ctree) t) (erased (Pz us0 ls H j p n t) pz)
      (erased (List (Pr us0 ls H j)) P) (erased (GSet) gs) (erased (List (Col)) rest) (erased (Nat) k) (erased (Apart (Nat) Lt p q) ap)
      (erased (PairCnt us0 ls H j P gs q rest k) pc) -> (PairCnt us0 ls H j (Cons (Pr us0 ls H j) (MkPr us0 ls H j p n bs t pz) P) gs q rest k)))

(def-fns _ $ (erased pc-hit : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j q n r) (erased (Bstack) bs) (erased (Ctree) u) (erased (Pz us0 ls H j q n u) pu)
    (erased (List (Pr us0 ls H j)) Q0) (erased (GSet) gs) (erased (List (Col)) rest) (erased (PairCnt us0 ls H j Q0 gs q rest r) pc) ->
    (erased (Nat) a k) (erased (MC gs bs rest a) m) (erased (Add a r k) ad)
    (erased (PairCnt us0 ls H j (Cons (Pr us0 ls H j) (MkPr us0 ls H j q n bs u pu) Q0) gs q rest k) pk))
  (let ((erased a) (erased m)) (mc-exists gs bs rest))
  (let ((erased k) (erased ad)) (add a r))
  (values a k m ad (PaHit us0 ls H j q n bs u pu Q0 gs rest a r k m pc ad)))

(def-fns _ $ (erased ch-symc : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n q r) (erased (Gsym) s) (erased (Bstack) bs) (erased (Ctree) t)
    (erased (Pz us0 ls H (Succ j) p n t) pz) (erased (List (Pr us0 ls H j)) Q0 Q) (erased (GSet) gs) (erased (Col) e) (erased (List (Col)) rest)
    (erased (Ch us0 ls H j s (MkPr us0 ls H (Succ j) p n bs t pz) Q0 Q) ch) (erased (Kid p e q) kq) (erased (PairCnt us0 ls H j Q0 gs q rest r) pc) ->
    (erased (Nat) c k) (erased (SymC s bs e gs rest c) sc) (erased (Add c r k) ad) (erased (PairCnt us0 ls H j Q gs q rest k) pk))
  (match erased ch _
    ((ChSkip _ _ _ _ _ _ q1 c1 _ _ u1 _ pu1 k1 _)
      (let-match erased (kid-dec p q1 q (C1) e k1 kq) (KcSame _ _)
        ((KcNe _ _ _ _ ne ap)
          (values (Zero) r (ScN (GSkip) bs e gs rest (match erased ne _ ((N12) (NsSk2 bs)) ((N13) (NsSk3 bs)))) (AddZero r)
            (PaMiss us0 ls H j q1 c1 q bs u1 pu1 Q0 gs rest r ap pc))))
      (let ((erased a) (erased k) (erased m) (erased ad) (erased pk)) (pc-hit us0 ls H j q c1 r bs u1 pu1 Q0 gs rest pc))
      (values a k (ScY (GSkip) bs bs (C1) gs rest a (SSkip bs) m) ad pk))
    ((ChPush _ _ _ _ _ _ q3 q4 c3 c4 _ _ u3 u4 _ b3 b4 k3 k4 _)
      (match erased (kid-dec p q3 q (C2) e k3 kq) _
        ((KcSame _ _)
          (let-match erased (kid-dec p q4 q (C3) (C2) k4 kq) (KcNe _ _ _ _ _ ap4))
          (let ((erased a) (erased k) (erased m) (erased ad) (erased pk))
            (pc-hit us0 ls H j q c3 r (BP0 bs) u3 b3 _ gs rest (PaMiss us0 ls H j q4 c4 q (BP1 bs) u4 b4 Q0 gs rest r ap4 pc)))
          (values a k (ScY (GPush) bs (BP0 bs) (C2) gs rest a (SPush2 bs) m) ad pk))
        ((KcNe _ _ _ _ ne3 ap3)
          (match erased (kid-dec p q4 q (C3) e k4 kq) _
            ((KcSame _ _)
              (let ((erased a) (erased k) (erased m) (erased ad) (erased pk)) (pc-hit us0 ls H j q c4 r (BP1 bs) u4 b4 Q0 gs rest pc))
              (values a k (ScY (GPush) bs (BP1 bs) (C3) gs rest a (SPush3 bs) m) ad (PaMiss us0 ls H j q3 c3 q (BP0 bs) u3 b3 _ gs rest k ap3 pk)))
            ((KcNe _ _ _ _ ne4 ap4)
              (let-match erased ne3 (N21) (absurd (N23) ne4))
              (values (Zero) r (ScN (GPush) bs (C1) gs rest (NsPu1 bs)) (AddZero r)
                (PaMiss us0 ls H j q3 c3 q (BP0 bs) u3 b3 _ gs rest r ap3 (PaMiss us0 ls H j q4 c4 q (BP1 bs) u4 b4 Q0 gs rest r ap4 pc))))))))
    ((ChPop _ _ _ _ _ _ q1 c1 _ e2 _ b1 _ u1 _ pu1 pp y k1 _)
      (let-match erased (kid-dec p q1 q e2 e k1 kq) (KcSame _ _)
        ((KcNe _ _ _ _ ne ap)
          (values (Zero) r (ScN s bs e gs rest (pop-nosym s bs b1 e2 e pp y ne)) (AddZero r) (PaMiss us0 ls H j q1 c1 q b1 u1 pu1 Q0 gs rest r ap pc))))
      (let ((erased a) (erased k) (erased m) (erased ad) (erased pk)) (pc-hit us0 ls H j q c1 r b1 u1 pu1 Q0 gs rest pc))
      (values a k (ScY s bs b1 e gs rest a y m) ad pk))
    ((ChNone _ _ _ _ _ _ _ _ ip _ _)
      (values (Zero) r (ScN s bs e gs rest (match erased ip _ ((IP0) (NsP0E e)) ((IP1) (NsP1E e)))) (AddZero r) pc))))

(def-fns _ $ (erased ch-miss : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n q q2 r) (erased (Gsym) s) (erased (Bstack) bs) (erased (Ctree) t)
    (erased (Pz us0 ls H (Succ j) p n t) pz) (erased (List (Pr us0 ls H j)) Q0 Q) (erased (GSet) gs) (erased (Col) e) (erased (List (Col)) rest)
    (erased (Ch us0 ls H j s (MkPr us0 ls H (Succ j) p n bs t pz) Q0 Q) ch) (erased (Apart (Nat) Lt p q) ap) (erased (Kid q e q2) kq)
    (erased (PairCnt us0 ls H j Q0 gs q2 rest r) pc) -> (erased (PairCnt us0 ls H j Q gs q2 rest r) pk))
  (match erased ch _
    ((ChSkip _ _ _ _ _ _ q1 c1 _ _ u1 _ pu1 k1 _) (PaMiss us0 ls H j q1 c1 q2 bs u1 pu1 Q0 gs rest r (kid-apart p q q1 q2 (C1) e ap k1 kq) pc))
    ((ChPush _ _ _ _ _ _ q3 q4 c3 c4 _ _ u3 u4 _ b3 b4 k3 k4 _)
      (PaMiss us0 ls H j q3 c3 q2 (BP0 bs) u3 b3 _ gs rest r (kid-apart p q q3 q2 (C2) e ap k3 kq)
        (PaMiss us0 ls H j q4 c4 q2 (BP1 bs) u4 b4 Q0 gs rest r (kid-apart p q q4 q2 (C3) e ap k4 kq) pc)))
    ((ChPop _ _ _ _ _ _ q1 c1 _ e2 _ b1 _ u1 _ pu1 _ _ k1 _) (PaMiss us0 ls H j q1 c1 q2 b1 u1 pu1 Q0 gs rest r (kid-apart p q q1 q2 e2 e ap k1 kq) pc))
    ((ChNone _ _ _ _ _ _ _ _ _ _ _) pc)))

(def-fns _ $ (erased mc-sum : (erased (GSet) gs g0 g1 g2 g3) (erased (Bstack) bs) (erased (Col) e) (erased (List (Col)) rest) (erased (Nat) c0 c1 c2 c3 q q2)
    (erased (Kid q e q2) kq) (erased (GSel gs (GPush) g0) s0) (erased (GSel gs (GSkip) g1) s1) (erased (GSel gs (GPop0) g2) s2) (erased (GSel gs (GPop1) g3) s3)
    (erased (SymC (GPush) bs e g0 rest c0) y0) (erased (SymC (GSkip) bs e g1 rest c1) y1) (erased (SymC (GPop0) bs e g2 rest c2) y2)
    (erased (SymC (GPop1) bs e g3 rest c3) y3) -> (erased (Nat) n) (erased (Sum4 c0 c1 c2 c3 n) sm) (erased (MC gs bs (Cons (Col) e rest) n) r))
  (let ((erased none) (erased some)) (values symc-none symc-some))
  (match erased e _
    (absurd (C0) kq)
    ((C1)
      (let-match erased (none _ _ _ _ _ c0 y0 (NsPu1 bs)) (Refl _ _))
      (let-match erased (none _ _ _ _ _ c2 y2 (NsP01 bs)) (Refl _ _))
      (let-match erased (none _ _ _ _ _ c3 y3 (NsP11 bs)) (Refl _ _))
      (values c1 (MkSum4 (Zero) c1 (Zero) (Zero) c1 c1 c1 (AddZero c1) (add-zero-right c1) (add-zero-right c1))
        (MCSkip gs g1 bs rest c1 s1 (some _ _ bs _ _ _ c1 y1 (SSkip bs)))))
    ((C2)
      (let-match erased (none _ _ _ _ _ c1 y1 (NsSk2 bs)) (Refl _ _))
      (match erased bs _
        ((BS0)
          (let-match erased (none _ _ _ _ _ c2 y2 (NsP0E (C2))) (Refl _ _))
          (let-match erased (none _ _ _ _ _ c3 y3 (NsP1E (C2))) (Refl _ _))
          (values c0 (MkSum4 c0 (Zero) (Zero) (Zero) c0 c0 c0 (add-zero-right c0) (add-zero-right c0) (add-zero-right c0))
            (MCPush gs g0 (BP0 bs) (C2) rest c0 (SPush2 bs) s0 (some _ _ (BP0 bs) _ _ _ c0 y0 (SPush2 bs)))))
        ((BP0 b)
          (let-match erased (none _ _ _ _ _ c3 y3 (NsP12 b)) (Refl _ _))
          (let ((erased n) (erased ad) (erased sm) (erased _)) (sum4-pp c0 c2))
          (values n sm (MCPP gs g0 g2 bs b (BP0 bs) (GPop0) (C2) rest c0 c2 n (Popped0 b) (SPush2 bs) s0 (some _ _ (BP0 bs) _ _ _ c0 y0 (SPush2 bs))
            (SPop02 b) s2 (some _ _ b _ _ _ c2 y2 (SPop02 b)) ad)))
        ((BP1 b)
          (let-match erased (none _ _ _ _ _ c2 y2 (NsP02 b)) (Refl _ _))
          (let ((erased n) (erased ad) (erased _) (erased sm)) (sum4-pp c0 c3))
          (values n sm (MCPP gs g0 g3 bs b (BP0 bs) (GPop1) (C2) rest c0 c3 n (Popped1 b) (SPush2 bs) s0 (some _ _ (BP0 bs) _ _ _ c0 y0 (SPush2 bs))
            (SPop12 b) s3 (some _ _ b _ _ _ c3 y3 (SPop12 b)) ad)))))
    ((C3)
      (let-match erased (none _ _ _ _ _ c1 y1 (NsSk3 bs)) (Refl _ _))
      (match erased bs _
        ((BS0)
          (let-match erased (none _ _ _ _ _ c2 y2 (NsP0E (C3))) (Refl _ _))
          (let-match erased (none _ _ _ _ _ c3 y3 (NsP1E (C3))) (Refl _ _))
          (values c0 (MkSum4 c0 (Zero) (Zero) (Zero) c0 c0 c0 (add-zero-right c0) (add-zero-right c0) (add-zero-right c0))
            (MCPush gs g0 (BP1 bs) (C3) rest c0 (SPush3 bs) s0 (some _ _ (BP1 bs) _ _ _ c0 y0 (SPush3 bs)))))
        ((BP0 b)
          (let-match erased (none _ _ _ _ _ c2 y2 (NsP03 b)) (Refl _ _))
          (let ((erased n) (erased ad) (erased _) (erased sm)) (sum4-pp c0 c3))
          (values n sm (MCPP gs g0 g3 bs b (BP1 bs) (GPop1) (C3) rest c0 c3 n (Popped0 b) (SPush3 bs) s0 (some _ _ (BP1 bs) _ _ _ c0 y0 (SPush3 bs))
            (SPop13 b) s3 (some _ _ b _ _ _ c3 y3 (SPop13 b)) ad)))
        ((BP1 b)
          (let-match erased (none _ _ _ _ _ c3 y3 (NsP13 b)) (Refl _ _))
          (let ((erased n) (erased ad) (erased sm) (erased _)) (sum4-pp c0 c2))
          (values n sm (MCPP gs g0 g2 bs b (BP1 bs) (GPop0) (C3) rest c0 c2 n (Popped1 b) (SPush3 bs) s0 (some _ _ (BP1 bs) _ _ _ c0 y0 (SPush3 bs))
            (SPop03 b) s2 (some _ _ b _ _ _ c2 y2 (SPop03 b)) ad)))))))

(def-fns _ $ (erased sum4-add : (erased (Nat) c0 c1 c2 c3 r0 r1 r2 r3 k0 k1 k2 k3 a b k) (erased (Add c0 r0 k0) d0) (erased (Add c1 r1 k1) d1)
    (erased (Add c2 r2 k2) d2) (erased (Add c3 r3 k3) d3) (erased (Sum4 c0 c1 c2 c3 a) sa) (erased (Sum4 r0 r1 r2 r3 b) sb) (erased (Add a b k) ad)
    -> (erased (Sum4 k0 k1 k2 k3 k) r))
  (let-match erased sa (MkSum4 _ _ _ _ _ cx cy a1 a2 a3))
  (let-match erased sb (MkSum4 _ _ _ _ _ rx ry b1 b2 b3))
  (let ((erased kx) (erased e1)) (add k0 k1))
  (let ((erased ky) (erased e2)) (add kx k2))
  (let ((erased kz) (erased e3)) (add ky k3))
  (let ((erased f1)) (add-swap c0 r0 k0 c1 r1 k1 kx cx rx d0 d1 e1 a1 b1))
  (let ((erased f2)) (add-swap cx rx kx c2 r2 k2 ky cy ry f1 d2 e2 a2 b2))
  (let-match erased (add-fn a b kz k (add-swap cy ry ky c3 r3 k3 kz a b f2 d3 e3 a3 b3) ad) (Refl _ _))
  (MkSum4 k0 k1 k2 k3 k kx ky e1 e2 e3))

(def-fns _ $ (erased pcnt-split : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j q q2 c) (erased (List (Pr us0 ls H (Succ j))) P)
    (erased (GSet) gs g0 g1 g2 g3) (erased (GSel gs (GPush) g0) s0) (erased (GSel gs (GSkip) g1) s1) (erased (GSel gs (GPop0) g2) s2)
    (erased (GSel gs (GPop1) g3) s3) (erased (Col) e) (erased (List (Col)) rest) (erased (Kid q e q2) kq) (erased (List (Pr us0 ls H j)) Ps0 Ps1 Ps2 Ps3)
    (erased (Stp us0 ls H j (GPush) P Ps0) t0) (erased (Stp us0 ls H j (GSkip) P Ps1) t1) (erased (Stp us0 ls H j (GPop0) P Ps2) t2)
    (erased (Stp us0 ls H j (GPop1) P Ps3) t3) (subterm erased (PairCnt us0 ls H (Succ j) P gs q (Cons (Col) e rest) c) pc) ->
    (erased (Nat) k0 k1 k2 k3) (erased (PairCnt us0 ls H j Ps0 g0 q2 rest k0) p0) (erased (PairCnt us0 ls H j Ps1 g1 q2 rest k1) p1)
    (erased (PairCnt us0 ls H j Ps2 g2 q2 rest k2) p2) (erased (PairCnt us0 ls H j Ps3 g3 q2 rest k3) p3) (erased (Sum4 k0 k1 k2 k3 c) sm))
  (let ((erased z)) (Zero))
  (let-match erased t0 (StpCons _ _ _ _ _ x Pt Q0 _ u0 h0)
    ((StpNil _ _ _ _ _)
      (let-match erased t1 (StpNil _ _ _ _ _))
      (let-match erased t2 (StpNil _ _ _ _ _))
      (let-match erased t3 (StpNil _ _ _ _ _))
      (let-match erased pc (PaNil _ _ _ _ _ _ _))
      (values z z z z (PaNil us0 ls H j q2 g0 rest) (PaNil us0 ls H j q2 g1 rest) (PaNil us0 ls H j q2 g2 rest) (PaNil us0 ls H j q2 g3 rest)
        (MkSum4 z z z z z z z (AddZero z) (AddZero z) (AddZero z)))))
  (let-match erased t1 (StpCons _ _ _ _ _ _ _ Q1 _ u1 h1))
  (let-match erased t2 (StpCons _ _ _ _ _ _ _ Q2 _ u2 h2))
  (let-match erased t3 (StpCons _ _ _ _ _ _ _ Q3 _ u3 h3))
  (match erased pc _
    ((PaHit _ _ _ _ _ n bs t pz _ _ _ a cr _ m pc1 ad)
      (let ((erased r0) (erased r1) (erased r2) (erased r3) (erased w0) (erased w1) (erased w2) (erased w3) (erased sr))
        (pcnt-split us0 ls H j q q2 cr Pt gs g0 g1 g2 g3 s0 s1 s2 s3 e rest kq Q0 Q1 Q2 Q3 u0 u1 u2 u3 pc1))
      (let ((erased c0) (erased k0) (erased y0) (erased d0) (erased v0)) (ch-symc us0 ls H j q n q2 r0 (GPush) bs t pz Q0 Ps0 g0 e rest h0 kq w0))
      (let ((erased c1) (erased k1) (erased y1) (erased d1) (erased v1)) (ch-symc us0 ls H j q n q2 r1 (GSkip) bs t pz Q1 Ps1 g1 e rest h1 kq w1))
      (let ((erased c2) (erased k2) (erased y2) (erased d2) (erased v2)) (ch-symc us0 ls H j q n q2 r2 (GPop0) bs t pz Q2 Ps2 g2 e rest h2 kq w2))
      (let ((erased c3) (erased k3) (erased y3) (erased d3) (erased v3)) (ch-symc us0 ls H j q n q2 r3 (GPop1) bs t pz Q3 Ps3 g3 e rest h3 kq w3))
      (let ((erased n4) (erased sc) (erased mn)) (mc-sum gs g0 g1 g2 g3 bs e rest c0 c1 c2 c3 q q2 kq s0 s1 s2 s3 y0 y1 y2 y3))
      (let-match erased (mc-fn gs bs (Cons _ e rest) n4 a mn m) (Refl _ _))
      (values k0 k1 k2 k3 v0 v1 v2 v3 (sum4-add c0 c1 c2 c3 r0 r1 r2 r3 k0 k1 k2 k3 n4 cr c d0 d1 d2 d3 sc sr ad)))
    ((PaMiss _ _ _ _ p n _ bs t pz _ _ _ _ ap pc1)
      (let ((erased r0) (erased r1) (erased r2) (erased r3) (erased w0) (erased w1) (erased w2) (erased w3) (erased sr))
        (pcnt-split us0 ls H j q q2 c Pt gs g0 g1 g2 g3 s0 s1 s2 s3 e rest kq Q0 Q1 Q2 Q3 u0 u1 u2 u3 pc1))
      (values r0 r1 r2 r3 (ch-miss us0 ls H j p n q q2 r0 (GPush) bs t pz Q0 Ps0 g0 e rest h0 ap kq w0)
        (ch-miss us0 ls H j p n q q2 r1 (GSkip) bs t pz Q1 Ps1 g1 e rest h1 ap kq w1) (ch-miss us0 ls H j p n q q2 r2 (GPop0) bs t pz Q2 Ps2 g2 e rest h2 ap kq w2)
        (ch-miss us0 ls H j p n q q2 r3 (GPop1) bs t pz Q3 Ps3 g3 e rest h3 ap kq w3) sr))))

; No chromogram of gs matches a trace of j colours.
(def-adts $ (NoMC : ((GSet) gs) ((Nat) j) -> Type)
  enum
  (many NmE : (erased (Nat) j) -> (NoMC (GSG (GEmpty)) j))
  (many NmOne : (erased (Nat) j) -> (NoMC (GSOne) (Succ j)))
  (many NmG0 : (erased (Gtree) g) -> (NoMC (GSG g) (Zero)))
  (many NmLeaf : (erased (Gtree) g) (erased (Bits) q) (erased (Nat) j) (erased (LeafSet g q) l) -> (NoMC (GSG g) (Succ (Succ j)))))

(def-fns _ $ (erased nomc-mc : (erased (GSet) gs) (erased (Nat) j n) (erased (Bstack) bs) (erased (List (Col)) rest) (erased (NoMC gs j) z)
    (erased (Length (Col) rest j) le) (erased (MC gs bs rest n) m) -> (erased (Eq (Nat) n (Zero)) r))
  (match erased z _
    ((NmE _) (mc-zero bs rest n m))
    ((NmOne _) (let-match erased le (LengthCons _ e et _ _)) (mc-one-long bs e et n m))
    ((NmG0 _) (let-match erased le (LengthNil _)) (let-match erased m (MCNil _ _ _ rp)) (let-match erased rp (GRG _)) (Refl _ n))
    ((NmLeaf g q _ l)
      (let-match erased le (LengthCons _ e et _ le1))
      (let-match erased le1 (LengthCons _ e2 et2 _ _))
      (mc-leaf-long g q bs e e2 et2 n l m))))

(def-fns _ $ (erased pcnt-zero : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j q c) (erased (List (Pr us0 ls H j)) P) (erased (GSet) gs) (erased (List (Col)) rest)
    (erased (NoMC gs j) z) (erased (Length (Col) rest j) le) (subterm erased (PairCnt us0 ls H j P gs q rest c) pc) -> (erased (Eq (Nat) c (Zero)) r))
  (let-match erased pc (PaHit _ _ _ _ _ _ bs _ _ Pt _ _ a c1 _ m pc1 ad)
    ((PaNil _ _ _ _ _ _ _) (Refl _ c))
    ((PaMiss _ _ _ _ _ _ _ _ _ _ Pt _ _ _ _ pc1) (pcnt-zero us0 ls H j q c Pt gs rest z le pc1)))
  (let-match erased (nomc-mc gs j a bs rest z le m) (Refl _ _))
  (let-match erased (pcnt-zero us0 ls H j q c1 Pt gs rest z le pc1) (Refl _ _))
  (let-match erased ad (AddZero _))
  (Refl _ c))

; R is Q less some of its pairs whose trees are empty.
(def-adts $ (Flt : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) ((List (Pr us0 ls H j)) Q) ((List (Pr us0 ls H j)) R) -> Type)
  enum
  (many FtNil : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) -> (Flt us0 ls H j (Nil (Pr us0 ls H j)) (Nil (Pr us0 ls H j))))
  (many FtKeep : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (erased (Pr us0 ls H j) x) (erased (List (Pr us0 ls H j)) Q R) (erased (Flt us0 ls H j Q R) f)
      -> (Flt us0 ls H j (Cons (Pr us0 ls H j) x Q) (Cons (Pr us0 ls H j) x R)))
  (many FtDead : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j p n) (erased (Bstack) bs) (erased (Pz us0 ls H j p n (CEmpty)) pz)
      (erased (List (Pr us0 ls H j)) Q R) (erased (Flt us0 ls H j Q R) f)
      -> (Flt us0 ls H j (Cons (Pr us0 ls H j) (MkPr us0 ls H j p n bs (CEmpty) pz) Q) R)))

; R is P filtered, or nothing when gs is empty.
(def-adts $ (Pruned : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) ((GSet) gs) ((List (Pr us0 ls H j)) P) ((List (Pr us0 ls H j)) R) -> Type)
  enum
  (many PrKeep : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (erased (GSet) gs) (erased (List (Pr us0 ls H j)) P R) (erased (Flt us0 ls H j P R) f)
      -> (Pruned us0 ls H j gs P R))
  (many PrDrop : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (erased (List (Pr us0 ls H j)) P)
      -> (Pruned us0 ls H j (GSG (GEmpty)) P (Nil (Pr us0 ls H j)))))

(def-fns _ $ (erased flt-pc : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j q i n0 k) (erased (GSet) gs) (erased (List (Pr us0 ls H j)) P R)
    (erased (List (Col)) rest) (subterm erased (Flt us0 ls H j P R) f) (erased (PairCnt us0 ls H j P gs q rest k) pc) (erased (TIdx q rest i) ti)
    (erased (Length (Col) rest j) le) (erased (Ent us0 i n0) e0) ->
    (erased (Nat) k2) (erased (PairCnt us0 ls H j R gs q rest k2) pk) (erased (Bump n0 k k2) b))
  (match erased f _
    ((FtNil _ _ _ _) (values k pc (BmEq n0 k)))
    ((FtKeep _ _ _ _ _ Q R1 f1)
      (match erased pc _
        ((PaHit _ _ _ _ _ n bs t pz _ _ _ a c _ m pc1 ad)
          (let ((erased k1) (erased p1) (erased b1)) (flt-pc us0 ls H j q i n0 c gs Q R1 rest f1 pc1 ti le e0))
          (let ((erased k2) (erased ad2) (erased b2)) (bump-add n0 a c k1 k b1 ad))
          (values k2 (PaHit us0 ls H j q n bs t pz R1 gs rest a k1 k2 m p1 ad2) b2))
        ((PaMiss _ _ _ _ p n _ bs t pz _ _ _ _ ap pc1)
          (let ((erased k1) (erased p1) (erased b1)) (flt-pc us0 ls H j q i n0 k gs Q R1 rest f1 pc1 ti le e0))
          (values k1 (PaMiss us0 ls H j p n q bs t pz R1 gs rest k1 ap p1) b1))))
    ((FtDead _ _ _ _ p _ _ pz Q _ f1)
      (let-match erased pc (PaHit _ _ _ _ _ _ _ _ _ _ _ _ _ c _ _ pc1 _)
        ((PaMiss _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ pc1) (flt-pc us0 ls H j q i n0 k gs Q R rest f1 pc1 ti le e0)))
      (let-match erased pz (MkPz _ _ _ _ _ _ _ tb _ _))
      (let ((erased z) (erased zb) (erased x) (erased s)) (tally-sub us0 j q i (CEmpty) rest tb ti le))
      (let-match erased (sub-fn (CEmpty) rest z (Zero) s (empty-sub rest)) (Refl _ _))
      (let-match erased (ent-fn us0 i n0 (Zero) e0 (MkEnt us0 i (Zero) zb x)) (Refl _ _))
      (let ((erased k1) (erased p1) (erased _)) (flt-pc us0 ls H j q i n0 c gs Q R rest f1 pc1 ti le e0))
      (values k1 p1 (BmZ k k1)))))

(def-fns _ $ (erased prune-pc : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j q i n0 k) (erased (GSet) gs) (erased (List (Pr us0 ls H j)) P R)
    (erased (List (Col)) rest) (erased (Pruned us0 ls H j gs P R) pr) (erased (PairCnt us0 ls H j P gs q rest k) pc) (erased (TIdx q rest i) ti)
    (erased (Length (Col) rest j) le) (erased (Ent us0 i n0) e0) ->
    (erased (Nat) k2) (erased (PairCnt us0 ls H j R gs q rest k2) pk) (erased (Bump n0 k k2) b))
  (let-match erased pr (PrDrop _ _ _ _ _) ((PrKeep _ _ _ _ _ _ _ f) (flt-pc us0 ls H j q i n0 k gs P R rest f pc ti le e0)))
  (let-match erased (pcnt-zero us0 ls H j q k P gs rest (NmE j) le pc) (Refl _ _))
  (values k (PaNil us0 ls H j q gs rest) (BmEq n0 k)))

(def-adts $ (HitAll : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((List (Pr us0 ls H (Zero))) P) ((Sv) s) ((Sv) s2) -> Type)
  enum
  (many HaNil : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H) (erased (Sv) s) -> (HitAll us0 ls H (Nil (Pr us0 ls H (Zero))) s s))
  (many HaCons : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H p n) (erased (Bstack) bs) (erased (Ctree) t) (erased (Pz us0 ls H (Zero) p n t) pz)
      (erased (List (Pr us0 ls H (Zero))) P) (erased (Sv) s s1 s2) (erased (Tick p s s1) tk) (erased (HitAll us0 ls H P s1 s2) h)
      -> (HitAll us0 ls H (Cons (Pr us0 ls H (Zero)) (MkPr us0 ls H (Zero) p n bs t pz) P) s s2)))

; The walk of the pairs P down the chromograms gs, for traces of j more colours, takes s to s2.
(def-adts
  ((Wk : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) ((GSet) gs) ((List (Pr us0 ls H j)) P) ((Sv) s) ((Sv) s2) -> Type)
    enum
    (many WkNil : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (erased (GSet) gs) (erased (Sv) s) -> (Wk us0 ls H j gs (Nil (Pr us0 ls H j)) s s))
    (many WkZero : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (erased (GSet) gs) (erased (List (Pr us0 ls H j)) P) (erased (Sv) s) (erased (NoMC gs j) z)
        -> (Wk us0 ls H j gs P s s))
    (many WkHit : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H) (erased (List (Pr us0 ls H (Zero))) P) (erased (Sv) s s2) (erased (HitAll us0 ls H P s s2) h)
        -> (Wk us0 ls H (Zero) (GSOne) P s s2))
    (many WkStep : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (erased (GSet) gs) (erased (List (Pr us0 ls H (Succ j))) P) (erased (Sv) s0 s1 s2 s3 s4)
        (erased (WkSym us0 ls H j gs P (GPush) s0 s1) w0) (erased (WkSym us0 ls H j gs P (GSkip) s1 s2) w1) (erased (WkSym us0 ls H j gs P (GPop0) s2 s3) w2)
        (erased (WkSym us0 ls H j gs P (GPop1) s3 s4) w3) -> (Wk us0 ls H (Succ j) gs P s0 s4)))
  ((WkSym : ((List Cnt) us0) ((List (U8)) ls) ((Nat) H) ((Nat) j) ((GSet) gs) ((List (Pr us0 ls H (Succ j))) P) ((Gsym) sym) ((Sv) s) ((Sv) s2) -> Type)
    enum
    (many MkWkSym : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (erased (GSet) gs gs1) (erased (List (Pr us0 ls H (Succ j))) P) (erased (Gsym) sym)
        (erased (List (Pr us0 ls H j)) Ps1 Ps2) (erased (Sv) s s2) (erased (GSel gs sym gs1) sl) (erased (Stp us0 ls H j sym P Ps1) st)
        (erased (Pruned us0 ls H j gs1 Ps1 Ps2) pr) (erased (Wk us0 ls H j gs1 Ps2 s s2) w) -> (WkSym us0 ls H j gs P sym s s2))))

(def-fns _ $ (erased hitall-trace : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H) (erased (List (Pr us0 ls H (Zero))) P) (erased (Sv) s s2)
    (subterm erased (HitAll us0 ls H P s s2) ha) (erased (Nat) i n0 k c) (erased (TrS s i n0 k) tr)
    (erased (PairCnt us0 ls H (Zero) P (GSOne) i (Nil (Col)) c) pc) -> (erased (Nat) k2) (erased (Add k c k2) ad) (erased (TrS s2 i n0 k2) tr2))
  (match erased ha _
    ((HaNil _ _ _ _) (let-match erased pc (PaNil _ _ _ _ _ _ _)) (values k (add-zero-right k) tr))
    ((HaCons _ _ _ p _ _ _ _ Pt _ s1 _ tk ha1)
      (let-match erased pc (PaHit _ _ _ _ _ _ _ _ _ _ _ _ _ c1 _ m pc1 ad)
        ((PaMiss _ _ _ _ _ _ _ _ _ _ _ _ _ _ ap pc1) (hitall-trace us0 ls H Pt s1 s2 ha1 i n0 k c (tick-other p i n0 k s s1 tk ap tr) pc1)))
      (let-match erased m (MCNil _ _ _ rp))
      (let-match erased rp (GROne))
      (let-match erased ad (AddSucc _ _ _ a0))
      (let-match erased a0 (AddZero _))
      (let ((erased k2) (erased a2) (erased tr2)) (hitall-trace us0 ls H Pt s1 s2 ha1 i n0 (Succ k) c1 (tick-same i n0 k s s1 tk tr) pc1))
      (let-match erased a2 (AddSucc _ _ k3 a3))
      (values k2 (add-succ-right k c1 k3 a3) tr2))))

(def-fns _ $ (erased add4 : (erased (Nat) k k0 k1 k2 k3 a b c d s) (erased (Add k k0 a) p0) (erased (Add a k1 b) p1) (erased (Add b k2 c) p2)
    (erased (Add c k3 d) p3) (erased (Sum4 k0 k1 k2 k3 s) sm) -> (erased (Add k s d) r))
  (let-match erased sm (MkSum4 _ _ _ _ _ x y a1 a2 a3))
  (let ((erased x1) (erased q1) (erased r1)) (add-assoc k k0 k1 a b p0 p1))
  (let-match erased (add-fn k0 k1 x1 x q1 a1) (Refl _ _))
  (let ((erased y1) (erased q2) (erased r2)) (add-assoc k x k2 b c r1 p2))
  (let-match erased (add-fn x k2 y1 y q2 a2) (Refl _ _))
  (let ((erased z1) (erased q3) (erased r3)) (add-assoc k y k3 c d r2 p3))
  (let-match erased (add-fn y k3 z1 s q3 a3) (Refl _ _))
  r3)

(def-fns _ $ (erased wk-trace : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j i q n0 k c) (erased (GSet) gs) (erased (List (Pr us0 ls H j)) P) (erased (Sv) s s2)
    (subterm erased (Wk us0 ls H j gs P s s2) w) (erased (List (Col)) rest) (erased (TIdx q rest i) ti) (erased (Length (Col) rest j) le)
    (erased (Ent us0 i n0) e0) (erased (TrS s i n0 k) tr) (erased (PairCnt us0 ls H j P gs q rest c) pc) ->
    (erased (Nat) k2) (erased (Add k c k2) ad) (erased (TrS s2 i n0 k2) tr2))
  (match erased w _
    ((WkNil _ _ _ _ _ _) (let-match erased pc (PaNil _ _ _ _ _ _ _)) (values k (add-zero-right k) tr))
    ((WkZero _ _ _ _ _ _ _ z) (let-match erased (pcnt-zero us0 ls H j q c P gs rest z le pc) (Refl _ _)) (values k (add-zero-right k) tr))
    ((WkHit _ _ _ _ _ _ ha) (let-match erased le (LengthNil _)) (let-match erased ti (TINil _)) (hitall-trace us0 ls H P s s2 ha i n0 k c tr pc))
    ((WkStep _ _ _ j1 _ _ _ sa sb sc _ w0 w1 w2 w3)
      (let-match erased le (LengthCons _ e rest1 _ le1))
      (let-match erased ti (TICons _ q2 _ _ _ kq ti1))
      (let-match erased w0 (MkWkSym _ _ _ _ _ g0 _ _ Ps0 R0 _ _ sl0 st0 pr0 x0))
      (let-match erased w1 (MkWkSym _ _ _ _ _ g1 _ _ Ps1 R1 _ _ sl1 st1 pr1 x1))
      (let-match erased w2 (MkWkSym _ _ _ _ _ g2 _ _ Ps2 R2 _ _ sl2 st2 pr2 x2))
      (let-match erased w3 (MkWkSym _ _ _ _ _ g3 _ _ Ps3 R3 _ _ sl3 st3 pr3 x3))
      (let ((erased k0) (erased k1) (erased k2) (erased k3) (erased p0) (erased p1) (erased p2) (erased p3) (erased sm))
        (pcnt-split us0 ls H j1 q q2 c P gs g0 g1 g2 g3 sl0 sl1 sl2 sl3 e rest1 kq Ps0 Ps1 Ps2 Ps3 st0 st1 st2 st3 pc))
      (let ((erased f0) (erased o0) (erased b0)) (prune-pc us0 ls H j1 q2 i n0 k0 g0 Ps0 R0 rest1 pr0 p0 ti1 le1 e0))
      (let ((erased f1) (erased o1) (erased b1)) (prune-pc us0 ls H j1 q2 i n0 k1 g1 Ps1 R1 rest1 pr1 p1 ti1 le1 e0))
      (let ((erased f2) (erased o2) (erased b2)) (prune-pc us0 ls H j1 q2 i n0 k2 g2 Ps2 R2 rest1 pr2 p2 ti1 le1 e0))
      (let ((erased f3) (erased o3) (erased b3)) (prune-pc us0 ls H j1 q2 i n0 k3 g3 Ps3 R3 rest1 pr3 p3 ti1 le1 e0))
      (let ((erased ka1) (erased a01) (erased tra1)) (wk-trace us0 ls H j1 i q2 n0 k f0 g0 R0 s sa x0 rest1 ti1 le1 e0 tr o0))
      (let ((erased ka) (erased a0) (erased tra)) (bump-fix sa i n0 k k0 f0 ka1 b0 a01 tra1))
      (let ((erased kb1) (erased a11) (erased trb1)) (wk-trace us0 ls H j1 i q2 n0 ka f1 g1 R1 sa sb x1 rest1 ti1 le1 e0 tra o1))
      (let ((erased kb) (erased a1) (erased trb)) (bump-fix sb i n0 ka k1 f1 kb1 b1 a11 trb1))
      (let ((erased kc1) (erased a21) (erased trc1)) (wk-trace us0 ls H j1 i q2 n0 kb f2 g2 R2 sb sc x2 rest1 ti1 le1 e0 trb o2))
      (let ((erased kc) (erased a2) (erased trc)) (bump-fix sc i n0 kb k2 f2 kc1 b2 a21 trc1))
      (let ((erased kd1) (erased a31) (erased trd1)) (wk-trace us0 ls H j1 i q2 n0 kc f3 g3 R3 sc s2 x3 rest1 ti1 le1 e0 trc o3))
      (let ((erased kd) (erased a3) (erased trd)) (bump-fix s2 i n0 kc k3 f3 kd1 b3 a31 trd1))
      (values kd (add4 k k0 k1 k2 k3 ka kb kc kd c a0 a1 a2 a3 sm) trd))))

; Clearing, for each index of T in turn, its gone entry in ws when its count in us is not 0, gives ws2.
(def-adts $ (Clears : ((List (Nat)) T) ((List Cnt) us) ((List Cnt) ws) ((List Cnt) ws2) -> Type)
  enum
  (many ClsNil : (erased (List Cnt) us ws) -> (Clears (Nil (Nat)) us ws ws))
  (many ClsZ : (erased (Nat) j) (erased (List (Nat)) T) (erased (List Cnt) us ws ws2) (erased (Ent us j (Zero)) e) (erased (Clears T us ws ws2) f)
      -> (Clears (Cons (Nat) j T) us ws ws2))
  (many ClsS : (erased (Nat) j n1) (erased (List (Nat)) T) (erased (List Cnt) us ws ws1 ws2) (erased (Ent us j (Succ n1)) e) (erased (Upd ws j (Zero) ws1) u)
      (erased (Clears T us ws1 ws2) f) -> (Clears (Cons (Nat) j T) us ws ws2)))

; x is x0 once cleared against the count n.
(def-adts $ (Fixed : ((Nat) n) ((Nat) x0) ((Nat) x) -> Type)
  enum
  (many FdS : (erased (Nat) n1 x0) -> (Fixed (Succ n1) x0 (Zero)))
  (many FdZ : (erased (Nat) x0) -> (Fixed (Zero) x0 x0)))

; The gone entry x of one index during the clearing: cleared, or still x0 with the index still to come in T.
(def-adts $ (Clr : ((Nat) n) ((Nat) x0) ((Nat) x) ((List (Nat)) T) ((Nat) i) -> Type)
  enum
  (many ClrDone : (erased (Nat) n x0 x i) (erased (List (Nat)) T) (erased (Fixed n x0 x) fd) -> (Clr n x0 x T i))
  (many ClrWait : (erased (Nat) n x0 i) (erased (List (Nat)) T) (erased (Elem (Nat) i T) el) -> (Clr n x0 x0 T i)))

(def-fns _ $ (erased has-clr : (erased (Nat) n x i) (erased (List (Nat)) T) (erased (HasT x T i) ht) -> (erased (Clr n x x T i) r))
  (match erased ht _
    ((HtZ _ _) (ClrDone n x x i T (match erased n _ ((Zero) (FdZ x)) ((Succ n1) (FdS n1 x)))))
    ((HtE _ _ _ el) (ClrWait n x i T el))))

(def-fns _ $ (erased clr-other : (erased (Nat) n x0 x i j) (erased (List (Nat)) T) (erased (Clr n x0 x (Cons (Nat) j T) i) p) (erased (Apart (Nat) Lt j i) ap)
    -> (erased (Clr n x0 x T i) r))
  (let-match erased p (ClrWait _ _ _ _ el) ((ClrDone _ _ _ _ _ fd) (ClrDone n x0 x i T fd)))
  (let-match erased el (ElThere _ _ _ _ el1) (absurd (ElHere _ _ _) (apart-irrefl i ap)))
  (ClrWait n x0 i T el1))

(def-fns _ $ (erased fix-trace : (erased (List (Nat)) T) (erased (List Cnt) us ws ws2) (subterm erased (Clears T us ws ws2) fx) (erased (Nat) i n x0 x)
    (erased (Ent us i n) eu) (erased (Ent ws i x) ew) (erased (Clr n x0 x T i) p) -> (erased (Nat) xf) (erased (Ent ws2 i xf) ef) (erased (Fixed n x0 xf) fd))
  (match erased fx _
    ((ClsNil _ _) (let-match erased p (ClrDone _ _ _ _ _ fd) (absurd (ClrWait _ _ _ _ el) el)) (values x ew fd))
    ((ClsZ j Tt _ _ _ ej fx1)
      (let-match erased (nat-eq j i) (Equal _ _ _)
        ((Unequal _ _ _ _ ap) (fix-trace Tt us ws ws2 fx1 i n x0 x eu ew (clr-other n x0 x i j Tt p ap))))
      (let-match erased (ent-fn us i n (Zero) eu ej) (Refl _ _))
      (fix-trace Tt us ws ws2 fx1 i n x0 x eu ew
        (ClrDone n x0 x i Tt (match erased p _ ((ClrDone _ _ _ _ _ fd) fd) ((ClrWait _ _ _ _ _) (FdZ x0))))))
    ((ClsS j n1 Tt _ _ ws1 _ ej uw fx1)
      (let-match erased (nat-eq j i) (Equal _ _ _)
        ((Unequal _ _ _ _ ap) (fix-trace Tt us ws1 ws2 fx1 i n x0 x eu (upd-other ws ws1 j (Zero) i x uw ap ew) (clr-other n x0 x i j Tt p ap))))
      (let-match erased (ent-fn us i n (Succ n1) eu ej) (Refl _ _))
      (fix-trace Tt us ws1 ws2 fx1 i n x0 (Zero) eu (upd-ent ws ws1 i (Zero) uw) (ClrDone n x0 (Zero) i Tt (FdS n1 x0))))))

; The gone entry g of a trace that had count n and keeps m: n if it lost its last count, otherwise 0.
(def-adts $ (GoneCnt : ((Nat) n) ((Nat) m) ((Nat) g) -> Type)
  enum
  (many GcGone : (erased (Nat) n) -> (GoneCnt n (Zero) n))
  (many GcKeep : (erased (Nat) n m1) -> (GoneCnt n (Succ m1) (Zero))))

(def-fns _ $ (erased gonecnt-fn : (erased (Nat) n m a b) (erased (GoneCnt n m a) p) (erased (GoneCnt n m b) q) -> (erased (Eq (Nat) a b) r))
  (match erased p _
    ((GcGone _) (let-match erased q (GcGone _)) (Refl _ a))
    ((GcKeep _ _) (let-match erased q (GcKeep _ _)) (Refl _ a))))

(def-fns _ $ (erased ds-final : (erased (Nat) n0 k n x0 xf) (erased (Ds n0 k n x0) st) (erased (Fixed n x0 xf) fd) ->
    (erased (Monus n0 k n) o) (erased (GoneCnt n0 n xf) gc))
  (let-match erased st (DsE _)
    ((DsU _) (values (MoZ n0) (match erased fd _ ((FdS n1 _) (GcKeep n0 n1)) ((FdZ _) (GcGone n0)))))
    ((DsT _ _ _ o) (values o (match erased fd _ ((FdS n1 _) (GcKeep n0 n1)) ((FdZ _) (GcGone n0))))))
  (let-match erased fd (FdZ _))
  (values (monus-zero k) (GcGone (Zero))))

; gone holds the traces of t of height j that keep lacks, with their counts in t.
(def-adts $ (GoneOf : ((Nat) j) ((Ctree) t) ((Ctree) keep) ((Ctree) gone) -> Type)
  enum
  (many GoE : (erased (Nat) j) (erased (Ctree) keep) -> (GoneOf j (CEmpty) keep (CEmpty)))
  (many GoL0 : (erased (Ctree) t) -> (GoneOf (Zero) t (CEmpty) t))
  (many GoL1 : (erased (Ctree) t lf) -> (GoneOf (Zero) t (CLeaf lf) (CEmpty)))
  (many GoN : (erased (Nat) j) (erased (Ctree) t1 t2 t3 keep k1 k2 k3 g1 g2 g3 gone) (erased (CtSel keep (C1) k1) s1) (erased (CtSel keep (C2) k2) s2)
      (erased (CtSel keep (C3) k3) s3) (erased (GoneOf j t1 k1 g1) o1) (erased (GoneOf j t2 k2 g2) o2) (erased (GoneOf j t3 k3 g3) o3)
      (erased (CtCons g1 g2 g3 gone) c) -> (GoneOf (Succ j) (CNode t1 t2 t3) keep gone)))

(def-fns _ $ (erased gone-sub : (erased (Nat) j n m) (erased (Ctree) t keep gone) (erased (List (Col)) et) (subterm erased (GoneOf j t keep gone) go)
    (erased (CtSub t et n) st) (erased (CtSub keep et m) sk) (erased (Length (Col) et j) le) -> (erased (Nat) g) (erased (CtSub gone et g) sg) (erased (GoneCnt n m g) gc))
  (match erased go _
    ((GoE _ _)
      (let-match erased (sub-fn (CEmpty) et n (Zero) st (empty-sub et)) (Refl _ _))
      (values (Zero) (empty-sub et) (match erased m _ ((Zero) (GcGone (Zero))) ((Succ m1) (GcKeep (Zero) m1)))))
    ((GoL0 _)
      (let-match erased le (LengthNil _))
      (let-match erased sk (SubNil _ _ rk))
      (let-match erased rk (RootE))
      (values n st (GcGone n)))
    ((GoL1 _ lf)
      (let-match erased le (LengthNil _))
      (let-match erased sk (SubNil _ _ rk))
      (let-match erased rk (RootL _ m1 _))
      (values (Zero) (SubNil (CEmpty) (Zero) (RootE)) (GcKeep n m1)))
    ((GoN j1 t1 t2 t3 _ k1 k2 k3 g1 g2 g3 _ s1 s2 s3 o1 o2 o3 c)
      (let-match erased le (LengthCons _ e et1 _ le1))
      (let-match erased st (SubCons _ u _ _ _ su st1))
      (let-match erased sk (SubCons _ v _ _ _ sv sk1))
      (match erased su _
        ((SelN0 _ _ _)
          (let-match erased (sub-fn (CEmpty) et1 n (Zero) st1 (empty-sub et1)) (Refl _ _))
          (let-match erased (sel0-empty keep v sv) (Refl _ _))
          (let-match erased (sub-fn (CEmpty) et1 m (Zero) sk1 (empty-sub et1)) (Refl _ _))
          (values (Zero) (SubCons gone (CEmpty) (C0) et1 (Zero) (cons-sel-back g1 g2 g3 gone (CEmpty) (C0) c (SelN0 g1 g2 g3)) (empty-sub et1))
            (GcGone (Zero))))
        ((SelN1 _ _ _)
          (let-match erased (sel-fn keep v k1 (C1) sv s1) (Refl _ _))
          (let ((erased g) (erased sg) (erased gc)) (gone-sub j1 n m t1 k1 g1 et1 o1 st1 sk1 le1))
          (values g (SubCons gone g1 (C1) et1 g (cons-sel-back g1 g2 g3 gone g1 (C1) c (SelN1 g1 g2 g3)) sg) gc))
        ((SelN2 _ _ _)
          (let-match erased (sel-fn keep v k2 (C2) sv s2) (Refl _ _))
          (let ((erased g) (erased sg) (erased gc)) (gone-sub j1 n m t2 k2 g2 et1 o2 st1 sk1 le1))
          (values g (SubCons gone g2 (C2) et1 g (cons-sel-back g1 g2 g3 gone g2 (C2) c (SelN2 g1 g2 g3)) sg) gc))
        ((SelN3 _ _ _)
          (let-match erased (sel-fn keep v k3 (C3) sv s3) (Refl _ _))
          (let ((erased g) (erased sg) (erased gc)) (gone-sub j1 n m t3 k3 g3 et1 o3 st1 sk1 le1))
          (values g (SubCons gone g3 (C3) et1 g (cons-sel-back g1 g2 g3 gone g3 (C3) c (SelN3 g1 g2 g3)) sg) gc))))))

(def-fns _ $ (erased cons-sel3 : (erased (Ctree) a1 a2 a3 t) (erased (CtCons a1 a2 a3 t) c) ->
    (erased (CtSel t (C1) a1) s1) (erased (CtSel t (C2) a2) s2) (erased (CtSel t (C3) a3) s3))
  (values (cons-sel-back a1 a2 a3 t a1 (C1) c (SelN1 a1 a2 a3)) (cons-sel-back a1 a2 a3 t a2 (C2) c (SelN2 a1 a2 a3))
    (cons-sel-back a1 a2 a3 t a3 (C3) c (SelN3 a1 a2 a3))))

(def-fns _ $ (erased gone-self : (erased (Nat) j) (erased (Ctree) t) (subterm erased (CtH j t) k) -> (erased (GoneOf j t t (CEmpty)) r))
  (let-match erased k (HN j1 t1 t2 t3 k1 k2 k3) ((HE _) (GoE j (CEmpty))) ((HL lf _) (GoL1 t lf)))
  (let ((erased e)) (CEmpty))
  (GoN j1 t1 t2 t3 t t1 t2 t3 e e e e (SelN1 t1 t2 t3) (SelN2 t1 t2 t3) (SelN3 t1 t2 t3) (gone-self j1 t1 k1) (gone-self j1 t2 k2) (gone-self j1 t3 k3)
    (CCEmpty)))

(def-fns _ $ (erased ife-tight : (erased (Ctree) t l) (erased (CtH (Zero) t) ht) (erased (CtH (Zero) l) hl) ->
    (erased (Ctree) g) (erased (IfE t l g) f) (erased (GoneOf (Zero) t l g) go) (erased (CtH (Zero) g) hg))
  (match erased l _
    ((CEmpty) (values t (IEY t) (GoL0 t) ht))
    ((CLeaf lf) (values (CEmpty) (IEN t l) (GoL1 t lf) (HE (Zero))))
    (absurd (CNode _ _ _) hl)))

(def-fns _ $ (erased gone-tight : (erased (Nat) h) (erased (Ctree) t keep gone) (erased (List RG) r) (subterm erased (CRes h t r keep gone) c)
    (erased (CtCanon (Succ h) t) ct) -> (erased (Ctree) gone2) (erased (CRes h t r keep gone2) c2) (erased (CtCanon (Succ h) gone2) cg)
    (erased (GoneOf (Succ h) t keep gone2) go))
  (match erased c _
    ((CRNil _ _) (values (CEmpty) c (canon-empty (Succ h)) (gone-self (Succ h) t (canon-h (Succ h) t ct))))
    ((CRE _ _) (values (CEmpty) c (canon-empty (Succ h)) (GoE (Succ h) keep)))
    ((CRS h1 t1 t2 t3 a1 a2 a3 b1 b2 b3 _ _ _ r1 r2 r3 s1 s2 s3 c1 c2 c3 ck _)
      (let-match erased ct (CanN _ _ _ _ _ q1 q2 q3 cn))
      (let-match erased cn (CnN _ _ _ _))
      (let ((erased e1) (erased d1) (erased n1) (erased o1)) (gone-tight h1 t1 a1 b1 r1 c1 q1))
      (let ((erased e2) (erased d2) (erased n2) (erased o2)) (gone-tight h1 t2 a2 b2 r2 c2 q2))
      (let ((erased e3) (erased d3) (erased n3) (erased o3)) (gone-tight h1 t3 a3 b3 r3 c3 q3))
      (let ((erased g) (erased gc)) (cn-c e1 e2 e3))
      (let ((erased cs)) (cn-cons e1 e2 e3 g gc))
      (let ((erased k1) (erased k2) (erased k3)) (cons-sel3 a1 a2 a3 keep ck))
      (values g (CRS h1 t1 t2 t3 a1 a2 a3 e1 e2 e3 keep g r r1 r2 r3 s1 s2 s3 d1 d2 d3 ck cs) (CanN (Succ h1) e1 e2 e3 g n1 n2 n3 gc)
        (GoN (Succ h1) t1 t2 t3 keep a1 a2 a3 e1 e2 e3 g k1 k2 k3 o1 o2 o3 cs)))
    ((CRZ t1 t2 t3 l1 l2 l3 _ _ _ _ _ _ n1 n2 n3 p1 p2 p3 d1 d2 d3 ck _ _ _ _)
      (let-match erased ct (CanN _ _ _ _ _ q1 q2 q3 cn))
      (let-match erased cn (CnN _ _ _ _))
      (let-match erased q1 (CanL _ h1))
      (let-match erased q2 (CanL _ h2))
      (let-match erased q3 (CanL _ h3))
      (let-match erased d1 (MkDecrAll _ _ _ _ _ _ _ m1 _ _))
      (let-match erased d2 (MkDecrAll _ _ _ _ _ _ _ m2 _ _))
      (let-match erased d3 (MkDecrAll _ _ _ _ _ _ _ m3 _ _))
      (let ((erased e1) (erased f1) (erased o1) (erased y1)) (ife-tight t1 l1 h1 m1))
      (let ((erased e2) (erased f2) (erased o2) (erased y2)) (ife-tight t2 l2 h2 m2))
      (let ((erased e3) (erased f3) (erased o3) (erased y3)) (ife-tight t3 l3 h3 m3))
      (let ((erased g) (erased gc)) (cn-c e1 e2 e3))
      (let ((erased cs)) (cn-cons e1 e2 e3 g gc))
      (let ((erased k1) (erased k2) (erased k3)) (cons-sel3 l1 l2 l3 keep ck))
      (values g (CRZ t1 t2 t3 l1 l2 l3 e1 e2 e3 keep g r n1 n2 n3 p1 p2 p3 d1 d2 d3 ck f1 f2 f3 cs)
        (CanN (Zero) e1 e2 e3 g (CanL e1 y1) (CanL e2 y2) (CanL e3 y3) gc) (GoN (Zero) t1 t2 t3 keep l1 l2 l3 e1 e2 e3 g k1 k2 k3 o1 o2 o3 cs)))))

; Each index of T is a trace with a heap node.
(def-adts $ (TPs : ((List (U8)) ls) ((Nat) H) ((List (Nat)) T) -> Type)
  enum
  (many TPNil : (erased (List (U8)) ls) (erased (Nat) H) -> (TPs ls H (Nil (Nat))))
  (many TPCons : (erased (List (U8)) ls) (erased (Nat) H i n) (erased (List (Nat)) T) (erased (Nd ls H (Zero) i n) nd) (erased (TPs ls H T) tp)
      -> (TPs ls H (Cons (Nat) i T))))

; What the walk keeps true of its whole state: both arrays of length len, and T within them.
(def-adts $ (Glob : ((List (U8)) ls) ((Nat) H) ((Nat) len) ((Sv) s) -> Type)
  enum
  (many MkGlob : (erased (List (U8)) ls) (erased (Nat) H len) (erased (List Cnt) us ws) (erased (List (Nat)) T) (erased (Length Cnt us len) lu)
      (erased (Length Cnt ws len) lw) (erased (AllLt T len) al) (erased (TPs ls H T) tp) -> (Glob ls H len (MkSv us ws T))))

(def-fns _ $ (many tick-c : (erased (List (U8)) ls) (erased (Nat) H len) (many (Nat) i) (erased (Lt i len) il) (erased (Nat) n) (erased (Nd ls H (Zero) i n) nd)
    (erased (List Cnt) us ws) (unique (Array Cnt us) a) (unique (Array Cnt ws) g) (many (List (Nat)) T) (erased (Glob ls H len (MkSv us ws T)) gl) ->
    (erased (List Cnt) us2 ws2) (unique (Array Cnt us2) a2 at a) (unique (Array Cnt ws2) g2 at g) (many (List (Nat)) T2)
    (erased (Glob ls H len (MkSv us2 ws2 T2)) gl2) (erased (Tick i (MkSv us ws T) (MkSv us2 ws2 T2)) tk))
  (let-match erased gl (MkGlob _ _ _ _ _ _ lu lw al tp))
  (let ((erased ou) (erased xu)) (nth-exists _ us len i lu il))
  (let-match erased ou (MkCopy _ vu))
  (let-match erased vu (MkU62 n0 nb))
  (let ((many w) (unique a1)) (array-get _ us a i vu xu))
  (let-match many w (MkU62 m _))
  (let-match many m (Succ n1) ((Zero) (values us ws a1 g T gl (TkZ i us ws T (MkEnt us i (Zero) nb xu)))))
  (let ((erased us2) (unique a2) (erased uu) (erased lu2)) (put-cnt us a1 len lu i il n1 (lt-trans n1 (Succ n1) u62-modulus (lt-succ n1) nb)))
  (let ((erased og) (erased xg)) (nth-exists _ ws len i lw il))
  (let-match erased og (MkCopy _ vg))
  (let-match erased vg (MkU62 x0 xb))
  (let ((many wg) (unique g1)) (array-get _ ws g i vg xg))
  (let-match many wg (MkU62 mg _))
  (let ((erased eu)) (MkEnt us i (Succ n1) nb xu))
  (let-match many mg (Zero)
    ((Succ x1) (values us2 ws a2 g1 T (MkGlob ls H len us2 ws T lu2 lw al tp) (TkS i n1 x1 us ws us2 T eu (MkEnt ws i (Succ x1) xb xg) uu))))
  (let ((erased ws2) (unique g2) (erased uw) (erased lw2)) (put-cnt ws g1 len lw i il m nb))
  (values us2 ws2 a2 g2 (Cons _ i T)
    (MkGlob ls H len us2 ws2 (Cons _ i T) lu2 lw2 (ALCons i len T il al) (TPCons ls H i n T nd tp))
    (TkF i n1 us ws us2 ws2 T eu (MkEnt ws i (Zero) xb xg) uu uw)))

(def-fns _ $ (many hit-kid : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (many (Nat) p) (erased (Nat) n) (erased (Ctree) t) (erased (Pz us0 ls H (Succ (Zero)) p n t) pz) (many (Col) e) (erased (Nat) q c)
    (erased (Kid p e q) kp) (erased (Kid n e c) kn) (erased (List Cnt) us ws) (unique (Array Cnt us) a) (unique (Array Cnt ws) g)
    (many (List (Nat)) T) (erased (Glob ls H len (MkSv us ws T)) gl) ->
    (erased (Ctree) u) (erased (Pz us0 ls H (Zero) q (Succ c) u) pu) (erased (List Cnt) us2 ws2) (unique (Array Cnt us2) a2 at a)
    (unique (Array Cnt ws2) g2 at g) (many (List (Nat)) T2) (erased (Glob ls H len (MkSv us2 ws2 T2)) gl2) (erased (Tick q (MkSv us ws T) (MkSv us2 ws2 T2)) tk))
  (let ((erased u) (erased _) (erased pu)) (pz-down us0 ls H (Zero) p n q c t e pz kp kn))
  (let-match erased pu (MkPz _ _ _ _ _ _ _ ub _ nd))
  (let ((erased ql)) (tally-lt us0 (Zero) q len u ub l0))
  (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased tk))
    (tick-c ls H len (kid-c p e q kp (lt-trans _ _ _ ql lb)) ql (Succ c) nd us ws a g T gl))
  (values u pu us2 ws2 a2 g2 T2 gl2 tk))

(def-fns _ $ (many hit-step : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (many (Gsym) s) (erased (List (Pr us0 ls H (Succ (Zero)))) P) (subterm many (Ps us0 ls H (Succ (Zero)) P) ps) (erased (List Cnt) us ws)
    (unique (Array Cnt us) a) (unique (Array Cnt ws) g) (many (List (Nat)) T) (erased (Glob ls H len (MkSv us ws T)) gl) ->
    (erased (List Cnt) us2 ws2) (unique (Array Cnt us2) a2 at a) (unique (Array Cnt ws2) g2 at g) (many (List (Nat)) T2)
    (erased (Glob ls H len (MkSv us2 ws2 T2)) gl2) (erased (List (Pr us0 ls H (Zero))) Q) (erased (Stp us0 ls H (Zero) s P Q) st)
    (erased (HitAll us0 ls H Q (MkSv us ws T) (MkSv us2 ws2 T2)) h))
  (let ((erased s0)) (MkSv us ws T))
  (let-match many ps (PsCons _ _ _ _ p n bs t pz Pt pst) ((PsNil _ _ _ _) (values us ws a g T gl (Nil _) (StpNil us0 ls H (Zero) s) (HaNil us0 ls H s0))))
  (let ((erased x)) (MkPr us0 ls H (Succ (Zero)) p n bs t pz))
  (let ((erased q) (erased tq)) (thrice-exists p))
  (let ((erased c) (erased tc)) (thrice-exists n))
  (let ((erased z)) (Zero))
  (let ((erased q2) (erased q3) (erased c2) (erased c3)) (values (Succ q) (Succ (Succ q)) (Succ (Succ c)) (Succ (Succ (Succ c)))))
  (let ((erased k1) (erased k2) (erased k3)) (values (Ki1 p q tq) (Ki2 p q tq) (Ki3 p q tq)))
  (match many s _
    ((GSkip)
      (let ((erased u) (erased pu) (erased us1) (erased ws1) (unique a1) (unique g1) (many T1) (erased gl1) (erased tk))
        (hit-kid us0 ls H len l0 lb p n t pz (C1) q c k1 (Ki1 n c tc) us ws a g T gl))
      (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased Q0) (erased st0) (erased h0))
        (tail $ hit-step us0 ls H len l0 lb s Pt pst us1 ws1 a1 g1 T1 gl1))
      (values us2 ws2 a2 g2 T2 gl2 (Cons _ (MkPr us0 ls H z q (Succ c) bs u pu) Q0)
        (StpCons us0 ls H z s x Pt Q0 _ st0 (ChSkip us0 ls H z p n q (Succ c) bs t u pz pu k1 Q0))
        (HaCons us0 ls H q (Succ c) bs u pu Q0 s0 (MkSv us1 ws1 T1) (MkSv us2 ws2 T2) tk h0)))
    ((GPush)
      (let ((erased u2) (erased p2) (erased usa) (erased wsa) (unique aa) (unique ga) (many Ta) (erased gla) (erased tka))
        (hit-kid us0 ls H len l0 lb p n t pz (C2) q2 (Succ c) k2 (Ki2 n c tc) us ws a g T gl))
      (let ((erased u3) (erased p3) (erased usb) (erased wsb) (unique ab) (unique gb) (many Tb) (erased glb) (erased tkb))
        (hit-kid us0 ls H len l0 lb p n t pz (C3) q3 (Succ (Succ c)) k3 (Ki3 n c tc) usa wsa aa ga Ta gla))
      (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased Q0) (erased st0) (erased h0))
        (tail $ hit-step us0 ls H len l0 lb s Pt pst usb wsb ab gb Tb glb))
      (let ((erased y3)) (MkPr us0 ls H z q3 c3 (BP1 bs) u3 p3))
      (values us2 ws2 a2 g2 T2 gl2 (Cons _ (MkPr us0 ls H z q2 c2 (BP0 bs) u2 p2) (Cons _ y3 Q0))
        (StpCons us0 ls H z s x Pt Q0 _ st0 (ChPush us0 ls H z p n q2 q3 c2 c3 bs t u2 u3 pz p2 p3 k2 k3 Q0))
        (HaCons us0 ls H q2 c2 (BP0 bs) u2 p2 (Cons _ y3 Q0) s0 (MkSv usa wsa Ta) (MkSv us2 ws2 T2) tka
          (HaCons us0 ls H q3 c3 (BP1 bs) u3 p3 Q0 (MkSv usa wsa Ta) (MkSv usb wsb Tb) (MkSv us2 ws2 T2) tkb h0))))
    ((GPop0)
      (match many bs _
        ((BS0)
          (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased Q0) (erased st0) (erased h0))
            (tail $ hit-step us0 ls H len l0 lb s Pt pst us ws a g T gl))
          (values us2 ws2 a2 g2 T2 gl2 Q0 (StpCons us0 ls H z s x Pt Q0 _ st0 (ChNone us0 ls H z p n s t (IP0) pz Q0)) h0))
        ((BP0 b)
          (let ((erased u) (erased pu) (erased us1) (erased ws1) (unique a1) (unique g1) (many T1) (erased gl1) (erased tk))
            (hit-kid us0 ls H len l0 lb p n t pz (C2) q2 (Succ c) k2 (Ki2 n c tc) us ws a g T gl))
          (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased Q0) (erased st0) (erased h0))
            (tail $ hit-step us0 ls H len l0 lb s Pt pst us1 ws1 a1 g1 T1 gl1))
          (values us2 ws2 a2 g2 T2 gl2 (Cons _ (MkPr us0 ls H z q2 c2 b u pu) Q0)
            (StpCons us0 ls H z s x Pt Q0 _ st0 (ChPop us0 ls H z p n q2 c2 s (C2) bs b t u pz pu (Popped0 b) (SPop02 b) k2 Q0))
            (HaCons us0 ls H q2 c2 b u pu Q0 s0 (MkSv us1 ws1 T1) (MkSv us2 ws2 T2) tk h0)))
        ((BP1 b)
          (let ((erased u) (erased pu) (erased us1) (erased ws1) (unique a1) (unique g1) (many T1) (erased gl1) (erased tk))
            (hit-kid us0 ls H len l0 lb p n t pz (C3) q3 (Succ (Succ c)) k3 (Ki3 n c tc) us ws a g T gl))
          (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased Q0) (erased st0) (erased h0))
            (tail $ hit-step us0 ls H len l0 lb s Pt pst us1 ws1 a1 g1 T1 gl1))
          (values us2 ws2 a2 g2 T2 gl2 (Cons _ (MkPr us0 ls H z q3 c3 b u pu) Q0)
            (StpCons us0 ls H z s x Pt Q0 _ st0 (ChPop us0 ls H z p n q3 c3 s (C3) bs b t u pz pu (Popped1 b) (SPop03 b) k3 Q0))
            (HaCons us0 ls H q3 c3 b u pu Q0 s0 (MkSv us1 ws1 T1) (MkSv us2 ws2 T2) tk h0)))))
    ((GPop1)
      (match many bs _
        ((BS0)
          (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased Q0) (erased st0) (erased h0))
            (tail $ hit-step us0 ls H len l0 lb s Pt pst us ws a g T gl))
          (values us2 ws2 a2 g2 T2 gl2 Q0 (StpCons us0 ls H z s x Pt Q0 _ st0 (ChNone us0 ls H z p n s t (IP1) pz Q0)) h0))
        ((BP0 b)
          (let ((erased u) (erased pu) (erased us1) (erased ws1) (unique a1) (unique g1) (many T1) (erased gl1) (erased tk))
            (hit-kid us0 ls H len l0 lb p n t pz (C3) q3 (Succ (Succ c)) k3 (Ki3 n c tc) us ws a g T gl))
          (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased Q0) (erased st0) (erased h0))
            (tail $ hit-step us0 ls H len l0 lb s Pt pst us1 ws1 a1 g1 T1 gl1))
          (values us2 ws2 a2 g2 T2 gl2 (Cons _ (MkPr us0 ls H z q3 c3 b u pu) Q0)
            (StpCons us0 ls H z s x Pt Q0 _ st0 (ChPop us0 ls H z p n q3 c3 s (C3) bs b t u pz pu (Popped0 b) (SPop13 b) k3 Q0))
            (HaCons us0 ls H q3 c3 b u pu Q0 s0 (MkSv us1 ws1 T1) (MkSv us2 ws2 T2) tk h0)))
        ((BP1 b)
          (let ((erased u) (erased pu) (erased us1) (erased ws1) (unique a1) (unique g1) (many T1) (erased gl1) (erased tk))
            (hit-kid us0 ls H len l0 lb p n t pz (C2) q2 (Succ c) k2 (Ki2 n c tc) us ws a g T gl))
          (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased Q0) (erased st0) (erased h0))
            (tail $ hit-step us0 ls H len l0 lb s Pt pst us1 ws1 a1 g1 T1 gl1))
          (values us2 ws2 a2 g2 T2 gl2 (Cons _ (MkPr us0 ls H z q2 c2 b u pu) Q0)
            (StpCons us0 ls H z s x Pt Q0 _ st0 (ChPop us0 ls H z p n q2 c2 s (C2) bs b t u pz pu (Popped1 b) (SPop12 b) k2 Q0))
            (HaCons us0 ls H q2 c2 b u pu Q0 s0 (MkSv us1 ws1 T1) (MkSv us2 ws2 T2) tk h0)))))))

(def-fns _ $ (many pr-kid : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (unique (Bytes ls) fa) (many (Nat) p n) (erased (Ctree) t) (erased (Pz us0 ls H (Succ j) p n t) pz) (many (Col) e) (erased (Nat) q c)
    (erased (Kid p e q) kp) (erased (Kid n e c) kn) (many (Bstack) bs) (erased (List (Pr us0 ls H j)) Q0 R0) (many (Ps us0 ls H j R0) rs0)
    (erased (Flt us0 ls H j Q0 R0) f0) ->
    (unique fa is fa2 at fa) (erased (Ctree) u) (erased (Pz us0 ls H j q (Succ c) u) pu) (erased (MkPr us0 ls H j q (Succ c) bs u pu) is y)
    (erased (List (Pr us0 ls H j)) R) (many (Ps us0 ls H j R) rs) (erased (Flt us0 ls H j (Cons (Pr us0 ls H j) y Q0) R) f))
  (let ((erased u) (erased _) (erased pu)) (pz-down us0 ls H j p n q c t e pz kp kn))
  (let ((erased y)) (MkPr us0 ls H j q (Succ c) bs u pu))
  (let-match erased pu (MkPz _ _ _ _ _ _ _ ub lv nd))
  (let-match erased nd (MkNd _ _ _ _ _ _ lenL _ _ _ _ _ ll lbl tf))
  (let ((erased nl)) (tfit-lt lenL j (Succ c) tf))
  (let ((erased nb)) (lt-trans _ _ _ nl lbl))
  (let ((many m)) (u62-inc (kid-c n e c kn (lt-trans _ _ _ (lt-succ c) nb)) nb))
  (let ((unique fa2) (erased v) (erased x) (many r)) (flag-get ls fa lenL ll m nl flag-live flag-one-lt8))
  (let-match many r (Unequal _ _ _ _ ap)
    ((Equal _ _ _)
      (values fa2 u pu y (Cons _ y R0) (PsCons us0 ls H j (kid-c p e q kp (lt-trans _ _ _ (tally-lt us0 j q len u ub l0) lb)) m bs u pu R0 rs0)
        (FtKeep us0 ls H j y Q0 R0 f0))))
  (let-match erased (lv-ne ls flag-live j (Succ c) v u lv x ap) (Refl _ _))
  (values fa2 u pu y R0 rs0 (FtDead us0 ls H j q (Succ c) bs pu Q0 R0 f0)))

(def-fns _ $ (many pr-pop : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (unique (Bytes ls) fa) (many (Nat) p n) (erased (Ctree) t) (erased (Pz us0 ls H (Succ j) p n t) pz) (erased (Gsym) s) (many (Col) e) (erased (Nat) q c)
    (erased (Kid p e q) kp) (erased (Kid n e c) kn) (erased (Bstack) bs) (many (Bstack) b) (erased (Popped bs b) pp) (erased (Sym s bs e b) y)
    (erased (List (Pr us0 ls H j)) Q0 R0) (many (Ps us0 ls H j R0) rs0) (erased (Flt us0 ls H j Q0 R0) f0) ->
    (unique fa is fa2 at fa) (erased (List (Pr us0 ls H j)) Q R) (many (Ps us0 ls H j R) rs)
    (erased (Ch us0 ls H j s (MkPr us0 ls H (Succ j) p n bs t pz) Q0 Q) ch) (erased (Flt us0 ls H j Q R) f))
  (let ((unique fa2) (erased u) (erased pu) (erased z) (erased R) (many rs) (erased f)) (pr-kid us0 ls H j len l0 lb fa p n t pz e q c kp kn b Q0 R0 rs0 f0))
  (values fa2 (Cons _ z Q0) R rs (ChPop us0 ls H j p n q (Succ c) s e bs b t u pz pu pp y kp Q0) f))

(def-fns _ $ (many pr-ch : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (unique (Bytes ls) fa) (many (Gsym) s) (many (Nat) p n) (many (Bstack) bs) (erased (Ctree) t) (erased (Pz us0 ls H (Succ j) p n t) pz)
    (erased (List (Pr us0 ls H j)) Q0 R0) (many (Ps us0 ls H j R0) rs0) (erased (Flt us0 ls H j Q0 R0) f0) ->
    (unique fa is fa2 at fa) (erased (List (Pr us0 ls H j)) Q R) (many (Ps us0 ls H j R) rs)
    (erased (Ch us0 ls H j s (MkPr us0 ls H (Succ j) p n bs t pz) Q0 Q) ch) (erased (Flt us0 ls H j Q R) f))
  (let ((erased q) (erased tq)) (thrice-exists p))
  (let ((erased c) (erased tc)) (thrice-exists n))
  (match many s _
    ((GSkip)
      (let ((unique fa2) (erased u) (erased pu) (erased z) (erased R) (many rs) (erased f))
        (pr-kid us0 ls H j len l0 lb fa p n t pz (C1) q c (Ki1 p q tq) (Ki1 n c tc) bs Q0 R0 rs0 f0))
      (values fa2 (Cons _ z Q0) R rs (ChSkip us0 ls H j p n q (Succ c) bs t u pz pu (Ki1 p q tq) Q0) f))
    ((GPush)
      (let ((unique fa1) (erased u3) (erased p3) (erased z3) (erased R3) (many rs3) (erased f3))
        (pr-kid us0 ls H j len l0 lb fa p n t pz (C3) (Succ (Succ q)) (Succ (Succ c)) (Ki3 p q tq) (Ki3 n c tc) (BP1 bs) Q0 R0 rs0 f0))
      (let ((unique fa2) (erased u2) (erased p2) (erased z2) (erased R2) (many rs2) (erased f2))
        (pr-kid us0 ls H j len l0 lb fa1 p n t pz (C2) (Succ q) (Succ c) (Ki2 p q tq) (Ki2 n c tc) (BP0 bs) (Cons _ z3 Q0) R3 rs3 f3))
      (values fa2 (Cons _ z2 (Cons _ z3 Q0)) R2 rs2
        (ChPush us0 ls H j p n (Succ q) (Succ (Succ q)) (Succ (Succ c)) (Succ (Succ (Succ c))) bs t u2 u3 pz p2 p3 (Ki2 p q tq) (Ki3 p q tq) Q0) f2))
    ((GPop0)
      (match many bs _
        ((BS0) (values fa Q0 R0 rs0 (ChNone us0 ls H j p n s t (IP0) pz Q0) f0))
        ((BP0 b) (pr-pop us0 ls H j len l0 lb fa p n t pz s (C2) (Succ q) (Succ c) (Ki2 p q tq) (Ki2 n c tc) bs b (Popped0 b) (SPop02 b) Q0 R0 rs0 f0))
        ((BP1 b) (pr-pop us0 ls H j len l0 lb fa p n t pz s (C3) (Succ (Succ q)) (Succ (Succ c)) (Ki3 p q tq) (Ki3 n c tc) bs b (Popped1 b) (SPop03 b) Q0 R0 rs0 f0))))
    ((GPop1)
      (match many bs _
        ((BS0) (values fa Q0 R0 rs0 (ChNone us0 ls H j p n s t (IP1) pz Q0) f0))
        ((BP0 b) (pr-pop us0 ls H j len l0 lb fa p n t pz s (C3) (Succ (Succ q)) (Succ (Succ c)) (Ki3 p q tq) (Ki3 n c tc) bs b (Popped0 b) (SPop13 b) Q0 R0 rs0 f0))
        ((BP1 b) (pr-pop us0 ls H j len l0 lb fa p n t pz s (C2) (Succ q) (Succ c) (Ki2 p q tq) (Ki2 n c tc) bs b (Popped1 b) (SPop12 b) Q0 R0 rs0 f0))))))

(def-fns _ $ (many pr-step : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (unique (Bytes ls) fa) (many (Gsym) s) (erased (List (Pr us0 ls H (Succ j))) P) (subterm many (Ps us0 ls H (Succ j) P) ps) ->
    (unique fa is fa2 at fa) (erased (List (Pr us0 ls H j)) Q R) (many (Ps us0 ls H j R) rs) (erased (Stp us0 ls H j s P Q) st) (erased (Flt us0 ls H j Q R) f))
  (let-match many ps (PsCons _ _ _ _ p n bs t pz Pt pst)
    ((PsNil _ _ _ _) (values fa (Nil _) (Nil _) (PsNil us0 ls H j) (StpNil us0 ls H j s) (FtNil us0 ls H j))))
  (let ((unique fa1) (erased Q0) (erased R0) (many rs0) (erased st0) (erased f0)) (notail $ pr-step us0 ls H j len l0 lb fa s Pt pst))
  (let ((unique fa2) (erased Q) (erased R) (many rs) (erased ch) (erased f)) (pr-ch us0 ls H j len l0 lb fa1 s p n bs t pz Q0 R0 rs0 f0))
  (values fa2 Q R rs (StpCons us0 ls H j s (MkPr us0 ls H (Succ j) p n bs t pz) Pt Q0 Q st0 ch) f))

(def-fns _ $ (many live-h : (erased (List (U8)) us) (unique (Bytes us) a) (erased (Nat) j) (many (Sx) x) (erased (GSet) gs) (erased (Gm us (Succ j) x gs) m) ->
    (unique a is a2 at a) (many (Sx) y) (erased (Gm us (Succ j) y gs) my) (erased (SxLive us y) ly))
  (let ((unique a2) (many c)) (live-c us a j x gs m))
  (match many c _ ((LcDead _ _) (values a2 (SxX) (GmX us (Succ j)) (LiX us))) ((LcLive _ _ _ l) (values a2 x m l))))

(def-fns _ $ (erased gtop-sel : (erased (Nat) j) (erased (GSet) a0 a1 a2 a3 gs a) (erased (Gsym) s) (erased (GTop j a0 a1 a2 a3 gs) tp)
    (erased (Pick4 (GSet) s a0 a1 a2 a3 a) pa) -> (erased (GSel gs s a) r))
  (match erased tp _
    ((GTN _ g0 g1 g2 g3)
      (match erased pa _
        ((PkPush _ _ _ _ _) (GSelN g0 g1 g2 g3 g0 s (PkPush _ g0 g1 g2 g3)))
        ((PkSkip _ _ _ _ _) (GSelN g0 g1 g2 g3 g1 s (PkSkip _ g0 g1 g2 g3)))
        ((PkPop0 _ _ _ _ _) (GSelN g0 g1 g2 g3 g2 s (PkPop0 _ g0 g1 g2 g3)))
        ((PkPop1 _ _ _ _ _) (GSelN g0 g1 g2 g3 g3 s (PkPop1 _ g0 g1 g2 g3)))))
    ((GTL g b0 b1 b2 b3 _ _ _ _ l q0 q1 q2 q3)
      (match erased pa _
        ((PkPush _ _ _ _ _) (GSelL g b0 b1 b2 b3 b0 s a l (PkPush _ b0 b1 b2 b3) q0))
        ((PkSkip _ _ _ _ _) (GSelL g b0 b1 b2 b3 b1 s a l (PkSkip _ b0 b1 b2 b3) q1))
        ((PkPop0 _ _ _ _ _) (GSelL g b0 b1 b2 b3 b2 s a l (PkPop0 _ b0 b1 b2 b3) q2))
        ((PkPop1 _ _ _ _ _) (GSelL g b0 b1 b2 b3 b3 s a l (PkPop1 _ b0 b1 b2 b3) q3))))))

(def-adts $ (SlC : ((GSet) gs) -> Type)
  enum
  (many SlOne : -> (SlC (GSOne)))
  (many SlNone : -> (SlC (GSG (GEmpty)))))

(def-fns _ $ (many slot-c : (erased (List (U8)) us) (unique (Bytes us) a) (many (Sx) o) (erased (GSet) gs) (erased (Gm us (Zero) o gs) m) ->
    (unique a is a2 at a) (many (SlC gs) c))
  (let-match many o (SxO i) ((SxX) (let-match erased m (GmX _ _)) (values a (SlNone))) (absurd (SxN _ _ _ _ _) m))
  (let ((erased v) (erased xe)) (gm-ent-o us (Zero) i gs m))
  (let ((unique a2) (many k)) (fent-at us a i v xe))
  (let-match many k (Succ k1) ((Zero) (let-match erased (gm-zero-o us (Zero) i gs m xe) (Refl _ _)) (values a2 (SlNone))))
  (let-match erased (gm-one-o us (Zero) i k1 gs m xe) (Refl _ _))
  (values a2 (SlOne)))

(def-fns _ $ (erased flt-all : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j) (subterm erased (List (Pr us0 ls H j)) Q) -> (erased (Flt us0 ls H j Q Q) f))
  (match erased Q _
    ((Nil _) (FtNil us0 ls H j))
    ((Cons _ x Q1) (FtKeep us0 ls H j x Q1 Q1 (flt-all us0 ls H j Q1)))))

(def-fns _ $ (many prep : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H j len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (unique (Bytes ls) fa) (many (Gsym) s) (erased (List (U8)) gts) (many (Sx) y) (erased (GSet) gs1) (erased (Gm gts j y gs1) m)
    (erased (List (Pr us0 ls H (Succ j))) P) (many (Ps us0 ls H (Succ j) P) ps) ->
    (unique fa is fa2 at fa) (erased (List (Pr us0 ls H j)) Ps1) (erased (Stp us0 ls H j s P Ps1) st) (erased (List (Pr us0 ls H j)) R)
    (many (Ps us0 ls H j R) rs) (erased (Pruned us0 ls H j gs1 Ps1 R) pr))
  (let-match many y (SxX) (else
    (let ((unique fa2) (erased Q) (erased R) (many rs) (erased st) (erased f)) (pr-step us0 ls H j len l0 lb fa s P ps))
    (values fa2 Q st R rs (PrKeep us0 ls H j gs1 Q R f))))
  (let-match erased m (GmX _ _))
  (let ((erased _) (erased Ps1) (erased _) (erased _) (erased st) (erased _)) (pr-step us0 ls H j len l0 lb fa s P ps))
  (values fa Ps1 st (Nil _) (PsNil us0 ls H j) (PrDrop us0 ls H j Ps1)))

(def-fns _ $ (many bot-sym : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (erased (Bytes ls) fa) (many (Gsym) s) (erased (GSet) gs) (erased (List (U8)) gts) (unique (Bytes gts) tq) (many (Sx) o) (erased (GSet) gs1)
    (erased (GSel gs s gs1) sl) (erased (Gm gts (Zero) o gs1) mo) (erased (List (Pr us0 ls H (Succ (Zero)))) P) (many (Ps us0 ls H (Succ (Zero)) P) ps)
    (erased (List Cnt) us ws) (unique (Array Cnt us) a)
    (unique (Array Cnt ws) g) (many (List (Nat)) T) (erased (Glob ls H len (MkSv us ws T)) gl) ->
    (unique tq is tq2 at tq) (erased (List Cnt) us2 ws2) (unique (Array Cnt us2) a2 at a) (unique (Array Cnt ws2) g2 at g) (many (List (Nat)) T2)
    (erased (Glob ls H len (MkSv us2 ws2 T2)) gl2) (erased (WkSym us0 ls H (Zero) gs P s (MkSv us ws T) (MkSv us2 ws2 T2)) w))
  (let ((erased s0)) (MkSv us ws T))
  (let ((unique tq2) (many oc)) (slot-c gts tq o gs1 mo))
  (let-match many oc (SlOne)
    ((SlNone)
      (let ((erased _) (erased Q) (erased _) (erased _) (erased st) (erased _)) (pr-step us0 ls H (Zero) len l0 lb fa s P ps))
      (values tq2 us ws a g T gl (MkWkSym us0 ls H (Zero) gs gs1 P s Q Q s0 s0 sl st (PrKeep us0 ls H (Zero) gs1 Q Q (flt-all us0 ls H (Zero) Q))
        (WkZero us0 ls H (Zero) gs1 Q s0 (NmG0 (GEmpty)))))))
  (let ((erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased Q) (erased st) (erased h)) (hit-step us0 ls H len l0 lb s P ps us ws a g T gl))
  (values tq2 us2 ws2 a2 g2 T2 gl2 (MkWkSym us0 ls H (Zero) gs gs1 P s Q Q s0 (MkSv us2 ws2 T2) sl st (PrKeep us0 ls H (Zero) gs1 Q Q (flt-all us0 ls H (Zero) Q))
    (WkHit us0 ls H Q s0 (MkSv us2 ws2 T2) h))))

(def-fns _ $ (many swalk : (erased (List Cnt) us0) (erased (List (U8)) ls) (erased (Nat) H len) (erased (Length Cnt us0 len) l0) (erased (Lt len u62-modulus) lb)
    (subterm many (Nat) j) (erased (List (U8)) gts) (unique (Bytes gts) tq) (many (Sx) x) (erased (GSet) gs) (erased (Gm gts (Succ j) x gs) mg)
    (erased (SxLive gts x) lv) (erased (List (Pr us0 ls H (Succ j))) P) (many (Ps us0 ls H (Succ j) P) ps) (unique (Bytes ls) fa) (erased (List Cnt) us ws) (unique (Array Cnt us) a)
    (unique (Array Cnt ws) g) (many (List (Nat)) T) (erased (Glob ls H len (MkSv us ws T)) gl) ->
    (unique fa is fa2 at fa) (unique tq is tq2 at tq) (erased (List Cnt) us2 ws2) (unique (Array Cnt us2) a2 at a) (unique (Array Cnt ws2) g2 at g)
    (many (List (Nat)) T2) (erased (Glob ls H len (MkSv us2 ws2 T2)) gl2) (erased (Wk us0 ls H (Succ j) gs P (MkSv us ws T) (MkSv us2 ws2 T2)) w))
  (let ((erased s)) (MkSv us ws T))
  (let-match many ps (PsCons _ _ _ _ _ _ _ _ _ _ _) ((PsNil _ _ _ _) (values fa tq us ws a g T gl (WkNil us0 ls H (Succ j) gs s))))
  (let-match many x (SxN i c0 c1 c2 c3)
    ((SxX) (let-match erased mg (GmX _ _)) (values fa tq us ws a g T gl (WkZero us0 ls H (Succ j) gs P s (NmE (Succ j)))))
    (absurd (SxO _) mg))
  (let-match erased lv (LiN _ _ v _ _ _ _ xe))
  (let ((erased e0) (erased e1) (erased e2) (erased e3) (erased m0) (erased m1) (erased m2) (erased m3) (erased tp)) (gm-one-n gts j i v c0 c1 c2 c3 gs mg xe))
  (let ((erased sl0) (erased sl1) (erased sl2) (erased sl3))
    (values (gtop-sel j e0 e1 e2 e3 gs e0 (GPush) tp (PkPush _ e0 e1 e2 e3)) (gtop-sel j e0 e1 e2 e3 gs e1 (GSkip) tp (PkSkip _ e0 e1 e2 e3))
      (gtop-sel j e0 e1 e2 e3 gs e2 (GPop0) tp (PkPop0 _ e0 e1 e2 e3)) (gtop-sel j e0 e1 e2 e3 gs e3 (GPop1) tp (PkPop1 _ e0 e1 e2 e3))))
  (match many j _
    ((Zero)
      (let ((unique tq1) (erased us1) (erased ws1) (unique a1) (unique g1) (many T1) (erased gl1) (erased x0))
        (bot-sym us0 ls H len l0 lb fa (GPush) gs gts tq c0 e0 sl0 m0 P ps us ws a g T gl))
      (let ((unique tq2) (erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased x1))
        (bot-sym us0 ls H len l0 lb fa (GSkip) gs gts tq1 c1 e1 sl1 m1 P ps us1 ws1 a1 g1 T1 gl1))
      (let ((unique tq3) (erased us3) (erased ws3) (unique a3) (unique g3) (many T3) (erased gl3) (erased x2))
        (bot-sym us0 ls H len l0 lb fa (GPop0) gs gts tq2 c2 e2 sl2 m2 P ps us2 ws2 a2 g2 T2 gl2))
      (let ((unique tq4) (erased us4) (erased ws4) (unique a4) (unique g4) (many T4) (erased gl4) (erased x3))
        (bot-sym us0 ls H len l0 lb fa (GPop1) gs gts tq3 c3 e3 sl3 m3 P ps us3 ws3 a3 g3 T3 gl3))
      (values fa tq4 us4 ws4 a4 g4 T4 gl4
        (WkStep us0 ls H (Zero) gs P s (MkSv us1 ws1 T1) (MkSv us2 ws2 T2) (MkSv us3 ws3 T3) (MkSv us4 ws4 T4) x0 x1 x2 x3)))
    ((Succ j1)
      (let ((unique tb0) (many y0) (erased my0) (erased ly0)) (live-h gts tq j1 c0 e0 m0))
      (let ((unique fb0) (erased Ps0) (erased st0) (erased R0) (many rs0) (erased pr0)) (prep us0 ls H j len l0 lb fa (GPush) gts y0 e0 my0 P ps))
      (let ((unique fa1) (unique tq1) (erased us1) (erased ws1) (unique a1) (unique g1) (many T1) (erased gl1) (erased x0))
        (notail $ swalk us0 ls H len l0 lb j1 gts tb0 y0 e0 my0 ly0 R0 rs0 fb0 us ws a g T gl))
      (let ((unique tb1) (many y1) (erased my1) (erased ly1)) (live-h gts tq1 j1 c1 e1 m1))
      (let ((unique fb1) (erased Ps1) (erased st1) (erased R1) (many rs1) (erased pr1)) (prep us0 ls H j len l0 lb fa1 (GSkip) gts y1 e1 my1 P ps))
      (let ((unique fa2) (unique tq2) (erased us2) (erased ws2) (unique a2) (unique g2) (many T2) (erased gl2) (erased x1))
        (notail $ swalk us0 ls H len l0 lb j1 gts tb1 y1 e1 my1 ly1 R1 rs1 fb1 us1 ws1 a1 g1 T1 gl1))
      (let ((unique tb2) (many y2) (erased my2) (erased ly2)) (live-h gts tq2 j1 c2 e2 m2))
      (let ((unique fb2) (erased Ps2) (erased st2) (erased R2) (many rs2) (erased pr2)) (prep us0 ls H j len l0 lb fa2 (GPop0) gts y2 e2 my2 P ps))
      (let ((unique fa3) (unique tq3) (erased us3) (erased ws3) (unique a3) (unique g3) (many T3) (erased gl3) (erased x2))
        (notail $ swalk us0 ls H len l0 lb j1 gts tb2 y2 e2 my2 ly2 R2 rs2 fb2 us2 ws2 a2 g2 T2 gl2))
      (let ((unique tb3) (many y3) (erased my3) (erased ly3)) (live-h gts tq3 j1 c3 e3 m3))
      (let ((unique fb3) (erased Ps3) (erased st3) (erased R3) (many rs3) (erased pr3)) (prep us0 ls H j len l0 lb fa3 (GPop1) gts y3 e3 my3 P ps))
      (let ((unique fa4) (unique tq4) (erased us4) (erased ws4) (unique a4) (unique g4) (many T4) (erased gl4) (erased x3))
        (tail $ swalk us0 ls H len l0 lb j1 gts tb3 y3 e3 my3 ly3 R3 rs3 fb3 us3 ws3 a3 g3 T3 gl3))
      (let ((erased s1) (erased s2) (erased s3) (erased s4)) (values (MkSv us1 ws1 T1) (MkSv us2 ws2 T2) (MkSv us3 ws3 T3) (MkSv us4 ws4 T4)))
      (values fa4 tq4 us4 ws4 a4 g4 T4 gl4
        (WkStep us0 ls H j gs P s s1 s2 s3 s4 (MkWkSym us0 ls H j gs e0 P (GPush) Ps0 R0 s s1 sl0 st0 pr0 x0)
          (MkWkSym us0 ls H j gs e1 P (GSkip) Ps1 R1 s1 s2 sl1 st1 pr1 x1) (MkWkSym us0 ls H j gs e2 P (GPop0) Ps2 R2 s2 s3 sl2 st2 pr2 x2)
          (MkWkSym us0 ls H j gs e3 P (GPop1) Ps3 R3 s3 s4 sl3 st3 pr3 x3))))))

(def-fns _ $ (many fix-c : (erased (Nat) len) (subterm many (List (Nat)) T) (erased (AllLt T len) al) (erased (List Cnt) us ws) (unique (Array Cnt us) a)
    (unique (Array Cnt ws) g) (erased (Length Cnt us len) lu) (erased (Length Cnt ws len) lw) ->
    (erased (List Cnt) ws2) (unique a is a2 at a) (unique (Array Cnt ws2) g2 at g) (erased (Length Cnt ws2 len) lw2) (erased (Clears T us ws ws2) fx))
  (let-match many T (Cons _ j Tt) ((Nil _) (values ws a g lw (ClsNil us ws))))
  (let-match erased al (ALCons _ _ _ jl al1))
  (let ((erased ou) (erased xu)) (nth-exists _ us len j lu jl))
  (let-match erased ou (MkCopy _ vu))
  (let-match erased vu (MkU62 n nb))
  (let ((many w) (unique a1)) (array-get _ us a j vu xu))
  (let-match many w (MkU62 m _))
  (let-match many m (Succ n1)
    ((Zero)
      (let ((erased ws2) (unique a2) (unique g2) (erased lw2) (erased fx)) (tail $ fix-c len Tt al1 us ws a1 g lu lw))
      (values ws2 a2 g2 lw2 (ClsZ j Tt us ws ws2 (MkEnt us j (Zero) nb xu) fx))))
  (let ((erased ws1) (unique g1) (erased uw) (erased lw1)) (put-cnt ws g len lw j jl (Zero) u62-modulus-pos))
  (let ((erased ws2) (unique a2) (unique g2) (erased lw2) (erased fx)) (tail $ fix-c len Tt al1 us ws1 a1 g1 lu lw1))
  (values ws2 a2 g2 lw2 (ClsS j n1 Tt us ws ws1 ws2 (MkEnt us j (Succ n1) nb xu) uw fx)))

; What a finished S walk from us and the zero array ws to us1 and ws2 established, with the restriction of ctu by gtr.
(def-adts $ (SDone : ((Nat) h) ((List Cnt) us1) ((List Cnt) ws2) ((Ctree) keep) ((Ctree) gone) ((List (Nat)) T) -> Type)
  enum
  (many MkSDone : (erased (Nat) h) (erased (Ctree) ctu keep gone) (erased (Gtree) gtr) (erased (List Cnt) us) (erased (List (U8)) ls) (erased (List Cnt) ws us1 ws1 ws2)
      (erased (List (Nat)) T)
      (erased (Pz us ls (Succ h) (Succ h) (Zero) (Zero) ctu) pz) (erased (Tally ws (Succ h) (Zero) (CEmpty)) wz)
      (erased (Wk us ls (Succ h) (Succ h) (GSG gtr) (Cons (Pr us ls (Succ h) (Succ h)) (MkPr us ls (Succ h) (Succ h) (Zero) (Zero) (BS0) ctu pz)
        (Nil (Pr us ls (Succ h) (Succ h)))) (MkSv us ws (Nil (Nat))) (MkSv us1 ws1 T)) w)
      (erased (Clears T us1 ws1 ws2) fx) (erased (CRes h ctu (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) keep gone) c) (erased (CtH (Succ h) ctu) hc)
      (erased (GoneOf (Succ h) ctu keep gone) go) -> (SDone h us1 ws2 keep gone T)))

; x is 0, or n is.
(def-adts $ (OneZ : ((Nat) n) ((Nat) x) -> Type)
  enum
  (many OzX : (erased (Nat) n) -> (OneZ n (Zero)))
  (many OzN : (erased (Nat) x) -> (OneZ (Zero) x)))

(def-fns _ $ (erased fixed-has : (erased (Nat) n x0 x i) (erased (List (Nat)) T) (erased (Fixed n x0 x) fd) (erased (HasT x0 T i) ht) -> (erased (HasT x T i) r))
  (match erased fd _ ((FdS _ _) (HtZ T i)) ((FdZ _) ht)))

(def-fns _ $ (erased trace-final : (erased (Nat) h i) (erased (List Cnt) us1 ws2) (erased (Ctree) keep gone) (erased (List (Nat)) T)
    (erased (SDone h us1 ws2 keep gone T) dn) (erased (List (Col)) et) (erased (TIdx (Zero) et i) ti) (erased (Length (Col) et (Succ h)) le) ->
    (erased (Nat) n x) (erased (Ent us1 i n) eu) (erased (CtSub keep et n) sk) (erased (Ent ws2 i x) ew) (erased (CtSub gone et x) sg)
    (erased (HasT x T i) hx) (erased (OneZ n x) oz))
  (let-match erased dn (MkSDone _ ctu _ _ gtr us ls ws _ ws1 _ _ pz wz w fx c hc go))
  (let-match erased pz (MkPz _ _ _ _ _ _ _ tb _ _))
  (let ((erased n0) (erased nb0) (erased x0) (erased s0)) (tally-sub us (Succ h) (Zero) i ctu et tb ti le))
  (let ((erased z) (erased zb) (erased xz) (erased sz)) (tally-sub ws (Succ h) (Zero) i (CEmpty) et wz ti le))
  (let-match erased (sub-fn (CEmpty) et z (Zero) sz (empty-sub et)) (Refl _ _))
  (let ((erased a) (erased m)) (mc-exists (GSG gtr) (BS0) et))
  (let ((erased e0)) (MkEnt us i n0 nb0 x0))
  (let ((erased k2) (erased ad) (erased tr))
    (wk-trace us ls (Succ h) (Succ h) i (Zero) n0 (Zero) a (GSG gtr) _ _ _ w et ti le e0
      (MkTrS us ws (Nil _) i n0 (Zero) n0 (Zero) e0 (MkEnt ws i (Zero) zb xz) (DsU n0) (HtZ (Nil _) i))
      (PaHit us ls (Succ h) (Succ h) (Zero) (Zero) (BS0) ctu pz (Nil _) (GSG gtr) et a (Zero) a m (PaNil us ls (Succ h) (Succ h) (Zero) (GSG gtr) et)
        (add-zero-right a))))
  (let-match erased ad (AddZero _))
  (let-match erased tr (MkTrS _ _ _ _ _ _ n xa eu ew st ht))
  (let ((erased x) (erased ew2) (erased fd)) (fix-trace T us1 ws1 ws2 fx i n xa xa eu ew (has-clr n xa i T ht)))
  (let ((erased o) (erased gc)) (ds-final n0 a n xa x st fd))
  (let-match erased (cres-sub h ctu keep gone (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) et n0 a c hc le s0
      (RCCons (BS0) gtr (Nil RG) et a (Zero) a m (RCNil et) (add-zero-right a))) (MkKeepSub _ _ _ _ m2 o2 sk))
  (let-match erased (monus-uniq n0 a n m2 o o2) (Refl _ _))
  (let ((erased g) (erased sg) (erased gc2)) (gone-sub (Succ h) n0 n ctu keep gone et go s0 sk le))
  (let-match erased (gonecnt-fn n0 n x g gc gc2) (Refl _ _))
  (values n x eu sk ew2 sg (fixed-has n xa x i T fd ht) (match erased gc _ ((GcGone _) (OzN x)) ((GcKeep _ _) (OzX n)))))

(def-fns _ $ (erased rev-exists : (subterm erased (List (Col)) pre) (erased (List (Col)) w) -> (erased (List (Col)) et) (erased (RevApp (Col) pre w et) ra))
  (let-match erased pre (Cons _ e pre1) ((Nil _) (values w (RANil _ w))))
  (let ((erased et) (erased ra)) (rev-exists pre1 (Cons _ e w)))
  (values et (RACons _ e pre1 w et ra)))

(def-fns _ $ (erased rev-len : (erased (List (Col)) pre w et) (erased (Nat) a b c) (subterm erased (RevApp (Col) pre w et) ra) (erased (Length (Col) pre a) la)
    (erased (Length (Col) w b) lw) (erased (Add a b c) ad) -> (erased (Length (Col) et c) r))
  (match erased ra _
    ((RANil _ _) (let-match erased la (LengthNil _)) (let-match erased ad (AddZero _)) lw)
    ((RACons _ e pre1 _ _ ra1)
      (let-match erased la (LengthCons _ _ _ a1 la1))
      (let-match erased ad (AddSucc _ _ c1 ad1))
      (rev-len pre1 (Cons _ e w) et a1 (Succ b) c ra1 la1 (LengthCons _ e w b lw) (add-succ-right a1 b c1 ad1)))))

; Each trace of j more colours from the prefix p has its entry 0 in ws, or lies in T.
(def-adts $ (ZoT : ((List Cnt) ws) ((List (Nat)) T) ((Nat) j) ((Nat) p) -> Type)
  enum
  (many ZtL : (erased (List Cnt) ws) (erased (List (Nat)) T) (erased (Nat) p x) (erased (Ent ws p x) e) (erased (HasT x T p) ht) -> (ZoT ws T (Zero) p))
  (many ZtN : (erased (List Cnt) ws) (erased (List (Nat)) T) (erased (Nat) j p q) (erased (Thrice p q) tq) (erased (ZoT ws T j q) z1)
      (erased (ZoT ws T j (Succ q)) z2) (erased (ZoT ws T j (Succ (Succ q))) z3) -> (ZoT ws T (Succ j) p)))

(def-fns _ $ (erased zot-step : (erased (List Cnt) ws ws2) (erased (List (Nat)) T) (erased (Nat) i j p) (subterm erased (ZoT ws (Cons (Nat) i T) j p) z)
    (erased (Upd ws i (Zero) ws2) u) -> (erased (ZoT ws2 T j p) r))
  (let-match erased z (ZtL _ _ _ x e ht)
    ((ZtN _ _ j1 _ q tq z1 z2 z3)
      (ZtN ws2 T j1 p q tq (zot-step ws ws2 T i j1 q z1 u) (zot-step ws ws2 T i j1 (Succ q) z2 u) (zot-step ws ws2 T i j1 (Succ (Succ q)) z3 u))))
  (let-match erased (nat-eq i p) (Unequal _ _ _ _ ap) ((Equal _ _ _) (ZtL ws2 T p (Zero) (upd-ent ws ws2 p (Zero) u) (HtZ T p))))
  (let ((erased e2)) (upd-other ws ws2 i (Zero) p x u ap e))
  (let-match erased ht (HtE _ _ _ el) ((HtZ _ _) (ZtL ws2 T p x e2 (HtZ T p))))
  (let-match erased el (ElThere _ _ _ _ el1) (absurd (ElHere _ _ _) (apart-irrefl p ap)))
  (ZtL ws2 T p x e2 (HtE x p T el1)))

(def-fns _ $ (erased zot-tally : (erased (List Cnt) ws) (erased (Nat) j p) (subterm erased (ZoT ws (Nil (Nat)) j p) z) -> (erased (Tally ws j p (CEmpty)) r))
  (match erased z _
    ((ZtL _ _ _ _ e ht)
      (let-match erased ht (HtZ _ _) (absurd (HtE _ _ _ el) el))
      (let-match erased e (MkEnt _ _ _ nb y))
      (TaL ws p (Zero) nb (CEmpty) y (RootE) (HE (Zero))))
    ((ZtN _ _ j1 _ q tq z1 z2 z3)
      (let ((erased c)) (CEmpty))
      (TaN ws j1 p q c c c c tq (zot-tally ws j1 q z1) (zot-tally ws j1 (Succ q) z2) (zot-tally ws j1 (Succ (Succ q)) z3) (CnE)))))

(def-fns _ $ (many zero-t : (erased (Nat) len j) (erased (List Cnt) ws) (unique (Array Cnt ws) g) (erased (Length Cnt ws len) lw) (subterm many (List (Nat)) T)
    (erased (AllLt T len) al) (erased (ZoT ws T j (Zero)) z) ->
    (erased (List Cnt) ws2) (unique (Array Cnt ws2) g2 at g) (erased (Length Cnt ws2 len) lw2) (erased (Tally ws2 j (Zero) (CEmpty)) wz))
  (let-match many T (Cons _ i Tt) ((Nil _) (values ws g lw (zot-tally ws j (Zero) z))))
  (let-match erased al (ALCons _ _ _ il al1))
  (let ((erased ws1) (unique g1) (erased u) (erased lw1)) (put-cnt ws g len lw i il (Zero) u62-modulus-pos))
  (tail $ zero-t len j ws1 g1 lw1 Tt al1 (zot-step ws ws1 Tt i j (Zero) z u)))

(def-fns _ $ (erased pw-both : (erased (Nat) h) (erased (List Cnt) us1 ws2) (erased (Ctree) keep gone) (erased (List (Nat)) T) (erased (SDone h us1 ws2 keep gone T) dn)
    (subterm erased (Nat) j) (erased (Nat) p d) (erased (List (Col)) pre) (erased (RIdx pre p) ri) (erased (Length (Col) pre d) lp)
    (erased (Add j d (Succ h)) ad) -> (erased (Pointwise us1 keep j p pre) pk) (erased (Pointwise ws2 gone j p pre) pg) (erased (ZoT ws2 T j p) zt))
  (let-match erased j (Succ j1)
    ((Zero)
      (let-match erased ad (AddZero _))
      (let ((erased et) (erased ra)) (rev-exists pre (Nil _)))
      (let ((erased ti)) (ridx-tidx pre (Nil _) et p p ri ra (TINil p)))
      (let ((erased n) (erased x) (erased eu) (erased sk) (erased ew) (erased sg) (erased hx) (erased _))
        (trace-final h p us1 ws2 keep gone T dn et ti (rev-len pre (Nil _) et d (Zero) d ra lp (LengthNil _) (add-zero-right d))))
      (let-match erased eu (MkEnt _ _ _ nb xn))
      (let-match erased ew (MkEnt _ _ _ xb xx))
      (values (PwL us1 keep p n nb pre et ra sk xn) (PwL ws2 gone p x xb pre et ra sg xx) (ZtL ws2 T p x ew hx))))
  (let-match erased ad (AddSucc _ _ _ ad1))
  (let ((erased ad2)) (add-succ-right j1 d h ad1))
  (let ((erased q) (erased tq)) (thrice-exists p))
  (let ((erased k1) (erased g1) (erased z1)) (pw-both h us1 ws2 keep gone T dn j1 q (Succ d) (Cons _ (C1) pre) (RICons pre p q (C1) ri (Ki1 p q tq)) (LengthCons _ (C1) pre d lp) ad2))
  (let ((erased k2) (erased g2) (erased z2))
    (pw-both h us1 ws2 keep gone T dn j1 (Succ q) (Succ d) (Cons _ (C2) pre) (RICons pre p (Succ q) (C2) ri (Ki2 p q tq)) (LengthCons _ (C2) pre d lp) ad2))
  (let ((erased k3) (erased g3) (erased z3))
    (pw-both h us1 ws2 keep gone T dn j1 (Succ (Succ q)) (Succ d) (Cons _ (C3) pre) (RICons pre p (Succ (Succ q)) (C3) ri (Ki3 p q tq)) (LengthCons _ (C3) pre d lp) ad2))
  (values (PwN us1 keep j1 p q pre tq k1 k2 k3) (PwN ws2 gone j1 p q pre tq g1 g2 g3) (ZtN ws2 T j1 p q tq z1 z2 z3)))

(def-fns _ $ (erased lv-decr : (erased (List (U8)) ls) (erased (Nat) g n k) (erased (Ctree) t l) (erased (List RG) r) (erased (Col) e)
    (erased (Lv ls g (Zero) n t) lv) (erased (CtRoot t k) rt) (erased (DecrAll r e k l) d) -> (erased (Lv ls g (Zero) n l) r2))
  (let-match erased d (MkDecrAll _ _ _ c kk _ q hl _ o))
  (let-match erased lv (LvE _ _ _ _) ((LvL _ _ _ _ x) (match erased hl _ ((HE _) (LvE ls g (Zero) n)) ((HL lf _) (LvL ls g n lf x)))))
  (let-match erased rt (RootE))
  (let-match erased (monus-uniq (Zero) kk c (Zero) o (monus-zero kk)) (Refl _ _))
  (match erased hl _ ((HE _) (LvE ls g (Zero) n)) (absurd (HL _ _) q)))

(def-fns _ $ (erased lv-cres : (erased (List (U8)) ls) (erased (Nat) g h n) (erased (Ctree) t keep gone) (erased (List RG) r)
    (subterm erased (CRes h t r keep gone) c) (erased (Lv ls g (Succ h) n t) lv) -> (erased (Lv ls g (Succ h) n keep) r2))
  (match erased c _
    ((CRNil _ _) lv)
    ((CRE _ _) (LvE ls g (Succ h) n))
    ((CRS h1 t1 t2 t3 a1 a2 a3 b1 b2 b3 _ _ _ r1 r2 r3 _ _ _ c1 c2 c3 ck _)
      (let-match erased lv (LvN _ _ _ _ q _ _ _ x tq l1 l2 l3))
      (match erased ck _
        ((CCEmpty) (LvE ls g (Succ h) n))
        ((CCNode _ _ _)
          (LvN ls g (Succ h1) n q a1 a2 a3 x tq (lv-cres ls g h1 (Succ q) t1 a1 b1 r1 c1 l1) (lv-cres ls g h1 (Succ (Succ q)) t2 a2 b2 r2 c2 l2)
            (lv-cres ls g h1 (Succ (Succ (Succ q))) t3 a3 b3 r3 c3 l3)))))
    ((CRZ t1 t2 t3 l1 l2 l3 _ _ _ _ _ _ n1 n2 n3 p1 p2 p3 d1 d2 d3 ck _ _ _ _)
      (let-match erased lv (LvN _ _ _ _ q _ _ _ x tq v1 v2 v3))
      (match erased ck _
        ((CCEmpty) (LvE ls g (Succ h) n))
        ((CCNode _ _ _)
          (LvN ls g (Zero) n q l1 l2 l3 x tq (lv-decr ls g (Succ q) n1 t1 l1 r (C1) v1 p1 d1) (lv-decr ls g (Succ (Succ q)) n2 t2 l2 r (C2) v2 p2 d2)
            (lv-decr ls g (Succ (Succ (Succ q))) n3 t3 l3 r (C3) v3 p3 d3)))))))

(def-fns _ $ (erased trace-dead : (erased (List Cnt) us) (erased (Nat) H i) (erased (Ctree) keep) (erased (List (Col)) pre) (erased (Tally us H (Zero) keep) tk)
    (erased (CtCanon H keep) kc) (erased (RIdx pre i) ri) (erased (Length (Col) pre H) le) (erased (Ent us i (Zero)) ez) -> (erased (CtAt keep pre (CEmpty)) r))
  (let ((erased u) (erased pt)) (ctat-exists keep pre))
  (let-match erased (canon-at (Zero) H H keep u pre kc pt le (add-zero-right H)) (CanL _ hu))
  (let ((erased et) (erased ra)) (rev-exists pre (Nil _)))
  (let ((erased ti)) (ridx-tidx pre (Nil _) et i i ri ra (TINil i)))
  (let ((erased n) (erased nb) (erased x) (erased s))
    (tally-sub us H (Zero) i keep et tk ti (rev-len pre (Nil _) et H (Zero) H ra le (LengthNil _) (add-zero-right H))))
  (let-match erased (ent-fn us i n (Zero) (MkEnt us i n nb x) ez) (Refl _ _))
  (let ((erased c) (erased rt)) (root-exists u))
  (let-match erased (sub-fn keep et c (Zero) (at-sub keep u pre (Nil _) et c pt ra (SubNil u c rt)) s) (Refl _ _))
  (match erased hu _ ((HE _) pt) (absurd (HL _ _) rt)))

(def-fns _ $ (many kill-up : (erased (Nat) H lenL) (erased (Ctree) keep) (erased (List (U8)) ls) (unique (Bytes ls) fa) (erased (Length (U8) ls lenL) ll)
    (erased (Lt lenL u62-modulus) lbl) (erased (TrieFit lenL H (Zero)) tf) (erased (CtCanon H keep) kc) (erased (Lv ls flag-live H (Zero) keep) lv)
    (many (Nat) m) (erased (Nat) d j) (subterm erased (List (Col)) pre) (erased (HIdx pre m) hm) (erased (Length (Col) pre d) le) (erased (Add d j H) ad)
    (erased (CtAt keep pre (CEmpty)) am) ->
    (erased (List (U8)) ls2) (unique (Bytes ls2) fa2 at fa) (erased (Length (U8) ls2 lenL) ll2) (erased (Lv ls2 flag-live H (Zero) keep) lv2))
  (let ((erased ml)) (tfit-lt lenL j m (tfit-at lenL j m d H pre tf hm le ad)))
  (let ((erased ls1) (unique fa1) (erased up) (erased ll1)) (put-fl ls fa lenL ll m ml (Zero) u8-modulus-pos))
  (let ((erased lvk)) (lv-kill ls ls1 flag-live H (Zero) m (Zero) keep keep (Nil _) pre lv (HxNil) (AtNil keep) up hm am))
  (let-match many m (Succ c) ((Zero) (values ls1 fa1 ll1 lvk)))
  (let-match erased hm (HxCons pre1 m1 _ e hm1 km))
  (let-match erased le (LengthCons _ _ _ d1 le1))
  (let-match erased ad (AddSucc _ _ Hq ad0))
  (let ((erased ad1)) (add-succ-right d1 j Hq ad0))
  (let ((erased cl)) (lt-trans c (Succ c) u62-modulus (lt-succ c) (lt-trans _ _ _ ml lbl)))
  (let ((many q) (erased k3) (erased r) (erased mm) (erased dq) (erased rl) (erased _)) (u62-div c (Succ (Succ (Succ (Zero)))) cl three-lt (LtZ _)))
  (let-match erased (kid-div m1 q c k3 r e km mm dq rl) (Refl _ _))
  (let-match erased (tfit-at lenL (Succ j) m1 d1 H pre1 tf hm1 le1 ad1) (TfN _ _ _ q3 _ tq f1 f2 f3))
  (let ((many c1) (erased c2-bd) (erased c3-bd)) (node-kids q q3 tq (lt-trans _ _ _ (tfit-lt _ _ _ f3) lbl)))
  (let ((many c2)) (u62-inc c1 c2-bd))
  (let ((many c3)) (u62-inc c2 c3-bd))
  (let ((unique fa2) (erased v1) (erased x1) (many r1)) (flag-get ls1 fa1 lenL ll1 c1 (tfit-lt _ _ _ f1) flag-live flag-one-lt8))
  (let-match many r1 (Unequal _ _ _ _ a1) ((Equal _ _ _) (values ls1 fa2 ll1 lvk)))
  (let ((unique fa3) (erased v2) (erased x2) (many r2)) (flag-get ls1 fa2 lenL ll1 c2 (tfit-lt _ _ _ f2) flag-live flag-one-lt8))
  (let-match many r2 (Unequal _ _ _ _ a2) ((Equal _ _ _) (values ls1 fa3 ll1 lvk)))
  (let ((unique fa4) (erased v3) (erased x3) (many r3)) (flag-get ls1 fa3 lenL ll1 c3 (tfit-lt _ _ _ f3) flag-live flag-one-lt8))
  (let-match many r3 (Unequal _ _ _ _ a3) ((Equal _ _ _) (values ls1 fa4 ll1 lvk)))
  (let-match erased am (AtCons _ u _ _ _ au _))
  (let-match erased (node-dead ls1 flag-live j q q3 v1 v2 v3 u (lv-at ls1 flag-live (Succ j) q d1 H keep u pre1 lvk hm1 au le1 ad1)
      (canon-at (Succ j) d1 H keep u pre1 kc au le1 ad1) tq x1 x2 x3 a1 a2 a3) (Refl _ _))
  (tail $ kill-up H lenL keep ls1 fa4 ll1 lbl tf kc lvk q d1 (Succ j) pre1 hm1 le1 ad1 au))

; o is the heap node of the first trie node at depth d.
(def-adts $ (Offs : ((Nat) d) ((Nat) o) -> Type)
  enum
  (many OfZ : -> (Offs (Zero) (Zero)))
  (many OfS : (erased (Nat) d o q) (erased (Offs d o) f) (erased (Thrice o q) t) -> (Offs (Succ d) (Succ q))))

(def-fns _ $ (many offs-c : (subterm many (Nat) d) -> (many (Nat) o) (erased (Offs d o) f))
  (let-match many d (Succ d1) ((Zero) (values (Zero) (OfZ))))
  (let ((many o1) (erased f1)) (notail $ offs-c d1))
  (let ((many x) (erased ax)) (add o1 o1))
  (let ((many q) (erased aq)) (add x o1))
  (values (Succ q) (OfS d1 o1 q f1 (adds-thrice o1 x q ax aq))))

(def-fns _ $ (erased thrice-add : (erased (Nat) o p n qo qp qn) (subterm erased (Thrice o qo) to) (erased (Thrice p qp) tp) (erased (Thrice n qn) tn)
    (erased (Add o p n) ad) -> (erased (Add qo qp qn) r))
  (match erased to _
    ((TZ) (let-match erased ad (AddZero _)) (let-match erased (thrice-fn p qp qn tp tn) (Refl _ _)) (AddZero qp))
    ((TS o1 q1 t1)
      (let-match erased ad (AddSucc _ _ m ad1))
      (let-match erased tn (TS _ qm tm))
      (AddSucc _ _ _ (AddSucc _ _ _ (AddSucc q1 qp qm (thrice-add o1 p m q1 qp qm t1 tp tm ad1)))))))

(def-fns _ $ (erased kid-add : (erased (Nat) qo p n q c qp qn) (erased (Col) e) (erased (Thrice p qp) tp) (erased (Thrice n qn) tn) (erased (Add qo qp qn) ad)
    (erased (Kid p e q) kp) (erased (Kid n e c) kn) -> (erased (Add qo q c) r))
  (match erased kp _
    ((Ki1 _ _ t1)
      (let-match erased kn (Ki1 _ _ t2))
      (let-match erased (thrice-fn p qp q tp t1) (Refl _ _))
      (let-match erased (thrice-fn n qn c tn t2) (Refl _ _))
      ad)
    ((Ki2 _ x t1)
      (let-match erased kn (Ki2 _ y t2))
      (let-match erased (thrice-fn p qp x tp t1) (Refl _ _))
      (let-match erased (thrice-fn n qn y tn t2) (Refl _ _))
      (add-succ-right qo qp qn ad))
    ((Ki3 _ x t1)
      (let-match erased kn (Ki3 _ y t2))
      (let-match erased (thrice-fn p qp x tp t1) (Refl _ _))
      (let-match erased (thrice-fn n qn y tn t2) (Refl _ _))
      (add-succ-right qo (Succ qp) (Succ qn) (add-succ-right qo qp qn ad)))))

(def-fns _ $ (erased hidx-off : (erased (List (Col)) pre) (erased (Nat) n p d o) (subterm erased (HIdx pre n) hi) (erased (RIdx pre p) ri)
    (erased (Length (Col) pre d) le) (erased (Offs d o) of) -> (erased (Add o p n) r))
  (match erased hi _
    ((HxNil) (let-match erased ri (RINil)) (let-match erased le (LengthNil _)) (let-match erased of (OfZ)) (AddZero (Zero)))
    ((HxCons pre1 n1 c e hi1 kn)
      (let-match erased ri (RICons _ p1 _ _ ri1 kp))
      (let-match erased le (LengthCons _ _ _ d1 le1))
      (let-match erased of (OfS _ o1 qo f1 to))
      (let ((erased qp) (erased tp)) (thrice-exists p1))
      (let ((erased qn) (erased tn)) (thrice-exists n1))
      (AddSucc qo p c (kid-add qo p1 n1 p c qp qn e tp tn (thrice-add o1 p1 n1 qo qp qn to tp tn (hidx-off pre1 n1 p1 d1 o1 hi1 ri1 le1 f1)) kp kn)))))

; Each node of the trie path pre holds g in gf.
(def-adts $ (Mkd : ((List (U8)) gf) ((Nat) g) ((List (Col)) pre) -> Type)
  enum
  (many MkdNil : (erased (List (U8)) gf) (erased (Nat) g) (erased (Fent gf (Zero) g) x) -> (Mkd gf g (Nil (Col))))
  (many MkdCons : (erased (List (U8)) gf) (erased (Nat) g n) (erased (Col) e) (erased (List (Col)) pre) (erased (HIdx (Cons (Col) e pre) n) hi)
      (erased (Fent gf n g) x) (erased (Mkd gf g pre) m) -> (Mkd gf g (Cons (Col) e pre))))

; gf2 is gf after writes of g alone.
(def-adts $ (WrG : ((List (U8)) gf) ((Nat) g) ((List (U8)) gf2) -> Type)
  enum
  (many WgNil : (erased (List (U8)) gf) (erased (Nat) g) -> (WrG gf g gf))
  (many WgCons : (erased (List (U8)) gf gf1 gf2) (erased (Nat) g y) (erased (WrG gf g gf1) w) (erased (Fupd gf1 y g gf2) u) -> (WrG gf g gf2)))

(def-fns _ $ (erased ent-wr : (erased (List (U8)) gf gf2) (erased (Nat) g n) (erased (Fent gf n g) x) (subterm erased (WrG gf g gf2) w) -> (erased (Fent gf2 n g) r))
  (let-match erased w (WgCons _ gf1 _ _ y w1 u) ((WgNil _ _) x))
  (let ((erased x1)) (ent-wr gf gf1 g n x w1))
  (match erased (nat-eq y n) _ ((Equal _ _ _) (fupd-ent gf1 gf2 n g u)) ((Unequal _ _ _ _ ap) (fupd-other gf1 gf2 y g n g u ap x1))))

(def-fns _ $ (erased mkd-wr : (erased (List (U8)) gf gf2) (erased (Nat) g) (erased (List (Col)) pre) (subterm erased (Mkd gf g pre) m) (erased (WrG gf g gf2) w)
    -> (erased (Mkd gf2 g pre) r))
  (match erased m _
    ((MkdNil _ _ x) (MkdNil gf2 g (ent-wr gf gf2 g (Zero) x w)))
    ((MkdCons _ _ n e pre1 hi x m1) (MkdCons gf2 g n e pre1 hi (ent-wr gf gf2 g n x w) (mkd-wr gf gf2 g pre1 m1 w)))))

(def-fns _ $ (erased wr-cat : (erased (List (U8)) gf gf1 gf2) (erased (Nat) g) (erased (WrG gf g gf1) a) (subterm erased (WrG gf1 g gf2) b) -> (erased (WrG gf g gf2) r))
  (match erased b _
    ((WgNil _ _) a)
    ((WgCons _ gf3 _ _ y b1 u) (WgCons gf gf3 gf2 g y (wr-cat gf gf1 gf3 g a b1) u))))

; Each trace of T whose count in us is 0 has its trie path pre hold g in gf.
(def-adts $ (Mks : ((List (U8)) gf) ((Nat) g) ((List Cnt) us) ((Nat) H) ((List (Nat)) T) -> Type)
  enum
  (many MksNil : (erased (List (U8)) gf) (erased (Nat) g) (erased (List Cnt) us) (erased (Nat) H) -> (Mks gf g us H (Nil (Nat))))
  (many MksLive : (erased (List (U8)) gf) (erased (Nat) g) (erased (List Cnt) us) (erased (Nat) H i k) (erased (List (Nat)) T) (erased (Ent us i (Succ k)) e)
      (erased (Mks gf g us H T) mk) -> (Mks gf g us H (Cons (Nat) i T)))
  (many MksDead : (erased (List (U8)) gf) (erased (Nat) g) (erased (List Cnt) us) (erased (Nat) H i) (erased (List (Col)) pre) (erased (List (Nat)) T)
      (erased (RIdx pre i) ri) (erased (Length (Col) pre H) le) (erased (Mkd gf g pre) m) (erased (Mks gf g us H T) mk) -> (Mks gf g us H (Cons (Nat) i T))))

(def-fns _ $ (erased mks-find : (erased (List (U8)) gf) (erased (List Cnt) us) (erased (Nat) g H i) (erased (List (Nat)) T) (subterm erased (Mks gf g us H T) mk)
    (erased (Elem (Nat) i T) el) (erased (Ent us i (Zero)) ez) ->
    (erased (List (Col)) pre) (erased (RIdx pre i) ri) (erased (Length (Col) pre H) le) (erased (Mkd gf g pre) m))
  (match erased mk _
    ((MksNil _ _ _ _) (match erased el _))
    ((MksLive _ _ _ _ _ k T1 e mk1)
      (let-match erased el (ElThere _ _ _ _ el1) (absurd (ElHere _ _ _) (ent-fn us i (Succ k) (Zero) e ez)))
      (mks-find gf us g H i T1 mk1 el1 ez))
    ((MksDead _ _ _ _ _ pre1 T1 ri le m mk1)
      (match erased el _
        ((ElHere _ _ _) (values pre1 ri le m))
        ((ElThere _ _ _ _ el1) (mks-find gf us g H i T1 mk1 el1 ez))))))

(def-fns _ $ (erased ridx-fn : (erased (List (Col)) pre pre2) (erased (Nat) p d) (subterm erased (RIdx pre p) a) (erased (RIdx pre2 p) b)
    (erased (Length (Col) pre d) la) (erased (Length (Col) pre2 d) lb) -> (erased (Eq (List (Col)) pre pre2) r))
  (match erased a _
    ((RINil) (let-match erased la (LengthNil _)) (let-match erased lb (LengthNil _)) (let-match erased b (RINil)) (Refl _ pre))
    ((RICons pre1 p1 _ e a1 k1)
      (let-match erased la (LengthCons _ _ _ d1 la1))
      (let-match erased lb (LengthCons _ _ pre3 _ lb1))
      (let-match erased b (RICons _ p3 _ e3 b1 k3))
      (let ((erased q1) (erased q2)) (kid-inj p1 p3 p e e3 k1 k3))
      (let-match erased q1 (Refl _ _))
      (let-match erased q2 (Refl _ _))
      (let-match erased (ridx-fn pre1 pre3 p1 d1 a1 b1 la1 lb1) (Refl _ _))
      (Refl _ pre))))

(def-fns _ $ (erased ridx-ext : (erased (List (Col)) pre w) (erased (Nat) p i) (erased (RIdx pre p) ri) (subterm erased (TIdx p w i) ti) ->
    (erased (List (Col)) pre2) (erased (RevApp (Col) w pre pre2) ra) (erased (RIdx pre2 i) r))
  (let-match erased ti (TICons _ q _ e w1 k ti1) ((TINil _) (values pre (RANil _ pre) ri)))
  (let ((erased pre2) (erased ra) (erased r)) (ridx-ext (Cons _ e pre) w1 q i (RICons pre p q e ri k) ti1))
  (values pre2 (RACons _ e w1 pre pre2 ra) r))

(def-fns _ $ (erased mkd-suffix : (erased (List (U8)) gf) (erased (Nat) g) (erased (List (Col)) w pre pre2) (subterm erased (RevApp (Col) w pre pre2) ra)
    (erased (Mkd gf g pre2) m) -> (erased (Mkd gf g pre) r))
  (let-match erased ra (RACons _ e w1 _ _ ra1) ((RANil _ _) m))
  (let-match erased (mkd-suffix gf g w1 (Cons _ e pre) pre2 ra1 m) (MkdCons _ _ _ _ _ _ _ m1))
  m1)

(def-fns _ $ (erased hidx-det : (erased (List (Col)) pre) (erased (Nat) n n2) (subterm erased (HIdx pre n) a) (erased (HIdx pre n2) b) -> (erased (Eq (Nat) n n2) r))
  (match erased a _
    ((HxNil) (let-match erased b (HxNil)) (Refl _ n))
    ((HxCons pre1 n1 c e a1 k1)
      (let-match erased b (HxCons _ n3 c3 _ b1 k3))
      (let-match erased (hidx-det pre1 n1 n3 a1 b1) (Refl _ _))
      (let-match erased (kid-dec n1 c c3 e e k1 k3) (KcSame _ _) (absurd (KcNe _ _ _ _ ne _) ne))
      (Refl _ n))))

(def-fns _ $ (erased mkd-ent : (erased (List (U8)) gf) (erased (Nat) g n) (erased (List (Col)) pre) (erased (Mkd gf g pre) m) (erased (HIdx pre n) hi)
    -> (erased (Fent gf n g) r))
  (match erased m _
    ((MkdNil _ _ x) (let-match erased hi (HxNil)) x)
    ((MkdCons _ _ n2 _ _ hi2 x _) (let-match erased (hidx-det pre n n2 hi hi2) (Refl _ _)) x)))

(def-fns _ $ (erased tally-mem : (erased (List Cnt) ws) (erased (Nat) j p) (erased (Ctree) t) (subterm erased (Tally ws j p t) tb) (erased (Occ t) o) ->
    (erased (List (Col)) et) (erased (Nat) i c) (erased (TIdx p et i) ti) (erased (Length (Col) et j) le) (erased (Ent ws i (Succ c)) e))
  (match erased tb _
    ((TaL _ _ n nb _ x rt k)
      (let-match erased o (OccL lf) (absurd (OccN _ _ _) k))
      (let-match erased rt (RootL _ c _))
      (values (Nil _) p c (TINil p) (LengthNil _) (MkEnt ws p (Succ c) nb x)))
    ((TaN _ j1 _ q t1 t2 t3 _ tq b1 b2 b3 cn)
      (let-match erased cn (CnN _ _ _ o3) (absurd (CnE) o))
      (match erased o3 _
        ((Occ1 _ _ _ o1)
          (let ((erased et) (erased i) (erased c) (erased ti) (erased le) (erased e)) (tally-mem ws j1 q t1 b1 o1))
          (values (Cons _ (C1) et) i c (TICons p q i (C1) et (Ki1 p q tq) ti) (LengthCons _ (C1) et j1 le) e))
        ((Occ2 _ _ _ o1)
          (let ((erased et) (erased i) (erased c) (erased ti) (erased le) (erased e)) (tally-mem ws j1 (Succ q) t2 b2 o1))
          (values (Cons _ (C2) et) i c (TICons p (Succ q) i (C2) et (Ki2 p q tq) ti) (LengthCons _ (C2) et j1 le) e))
        ((Occ3c _ _ _ o1)
          (let ((erased et) (erased i) (erased c) (erased ti) (erased le) (erased e)) (tally-mem ws j1 (Succ (Succ q)) t3 b3 o1))
          (values (Cons _ (C3) et) i c (TICons p (Succ (Succ q)) i (C3) et (Ki3 p q tq) ti) (LengthCons _ (C3) et j1 le) e))))))

(def-fns _ $ (erased mark-at : (erased (Nat) h) (erased (List Cnt) us1 ws2) (erased (List (U8)) gf) (erased (Ctree) keep gone t) (erased (List (Nat)) T) (erased (Nat) g j p n d)
    (erased (SDone h us1 ws2 keep gone T) dn) (erased (Mks gf g us1 (Succ h) T) mk) (erased (List (Col)) pre) (erased (Tally ws2 j p t) tb) (erased (Occ t) o)
    (erased (RIdx pre p) ri) (erased (HIdx pre n) hi) (erased (Length (Col) pre d) le) (erased (Add j d (Succ h)) ad) -> (erased (Fent gf n g) r))
  (let ((erased w) (erased i) (erased c) (erased ti) (erased lw) (erased e)) (tally-mem ws2 j p t tb o))
  (let ((erased pre2) (erased ra) (erased ri2)) (ridx-ext pre w p i ri ti))
  (let ((erased et) (erased ra2)) (rev-exists pre w))
  (let ((erased lf)) (rev-len pre w et d j (Succ h) ra2 le lw (add-comm j d (Succ h) ad)))
  (let ((erased n2) (erased x) (erased eu) (erased _) (erased ew) (erased _) (erased hx) (erased oz))
    (trace-final h i us1 ws2 keep gone T dn et (ridx-tidx pre w et p i ri ra2 ti) lf))
  (let-match erased (ent-fn ws2 i x (Succ c) ew e) (Refl _ _))
  (let-match erased hx (HtE _ _ _ el))
  (let-match erased oz (OzN _))
  (let ((erased pre3) (erased ri3) (erased le3) (erased m)) (mks-find gf us1 g (Succ h) i T mk el eu))
  (let-match erased (ridx-fn pre3 pre2 i (Succ h) ri3 ri2 le3 (rev-len w pre pre2 j d (Succ h) ra lw le ad)) (Refl _ _))
  (mkd-ent gf g n pre (mkd-suffix gf g w pre pre2 ra m) hi))

(def-fns _ $ (erased lv-marks : (erased (Nat) h) (erased (List Cnt) us1 ws2) (erased (List (U8)) gf) (erased (Ctree) keep gone t) (erased (List (Nat)) T) (erased (Nat) g j p n d)
    (erased (SDone h us1 ws2 keep gone T) dn) (erased (Mks gf g us1 (Succ h) T) mk) (erased (List (Col)) pre) (subterm erased (Tally ws2 j p t) tb)
    (erased (RIdx pre p) ri) (erased (HIdx pre n) hi) (erased (Length (Col) pre d) le) (erased (Add j d (Succ h)) ad) -> (erased (Lv gf g j n t) r))
  (match erased tb _
    ((TaL _ _ _ _ _ _ _ k)
      (match erased k _
        ((HE _) (LvE gf g (Zero) n))
        ((HL lf _) (LvL gf g n lf (mark-at h us1 ws2 gf keep gone t T g (Zero) p n d dn mk pre tb (OccL lf) ri hi le ad)))))
    ((TaN _ j1 _ q t1 t2 t3 _ tq b1 b2 b3 cn)
      (let-match erased cn (CnN _ _ _ _) ((CnE) (LvE gf g (Succ j1) n)))
      (let ((erased x)) (mark-at h us1 ws2 gf keep gone t T g (Succ j1) p n d dn mk pre tb (OccN t1 t2 t3) ri hi le ad))
      (let ((erased qn) (erased tn)) (thrice-exists n))
      (let-match erased ad (AddSucc _ _ Hq ad0))
      (let ((erased ad1)) (add-succ-right j1 d Hq ad0))
      (let ((erased le1)) (LengthCons _ (C1) pre d le))
      (let ((erased le2)) (LengthCons _ (C2) pre d le))
      (let ((erased le3)) (LengthCons _ (C3) pre d le))
      (LvN gf g j1 n qn t1 t2 t3 x tn
        (lv-marks h us1 ws2 gf keep gone t1 T g j1 q (Succ qn) (Succ d) dn mk (Cons _ (C1) pre) b1 (RICons pre p q (C1) ri (Ki1 p q tq))
          (HxCons pre n qn (C1) hi (Ki1 n qn tn)) le1 ad1)
        (lv-marks h us1 ws2 gf keep gone t2 T g j1 (Succ q) (Succ (Succ qn)) (Succ d) dn mk (Cons _ (C2) pre) b2 (RICons pre p (Succ q) (C2) ri (Ki2 p q tq))
          (HxCons pre n (Succ qn) (C2) hi (Ki2 n qn tn)) le2 ad1)
        (lv-marks h us1 ws2 gf keep gone t3 T g j1 (Succ (Succ q)) (Succ (Succ (Succ qn))) (Succ d) dn mk (Cons _ (C3) pre) b3
          (RICons pre p (Succ (Succ q)) (C3) ri (Ki3 p q tq)) (HxCons pre n (Succ (Succ qn)) (C3) hi (Ki3 n qn tn)) le3 ad1)))))

(def-fns _ $ (many mark-up : (erased (Nat) H lenG) (erased (List (U8)) gf) (unique (Bytes gf) ga) (erased (Length (U8) gf lenG) lg) (erased (Lt lenG u62-modulus) lbg)
    (erased (TrieFit lenG H (Zero)) tg) (many (Nat) g) (erased (Lt g u8-modulus) gb) (many (Nat) m) (erased (Nat) d j) (subterm erased (List (Col)) pre)
    (erased (HIdx pre m) hm) (erased (Length (Col) pre d) le) (erased (Add d j H) ad) ->
    (erased (List (U8)) gf2) (unique (Bytes gf2) ga2 at ga) (erased (Length (U8) gf2 lenG) lg2) (erased (Mkd gf2 g pre) mk) (erased (WrG gf g gf2) w))
  (let ((erased ml)) (tfit-lt lenG j m (tfit-at lenG j m d H pre tg hm le ad)))
  (let-match many m (Succ c)
    ((Zero)
      (let-match erased hm (HxNil))
      (let ((erased gf2) (unique ga2) (erased u) (erased lg2)) (put-fl gf ga lenG lg (Zero) ml g gb))
      (values gf2 ga2 lg2 (MkdNil gf2 g (fupd-ent gf gf2 (Zero) g u)) (WgCons gf gf gf2 g (Zero) (WgNil gf g) u))))
  (let-match erased hm (HxCons pre1 m1 _ e hm1 km))
  (let-match erased le (LengthCons _ _ _ d1 le1))
  (let-match erased ad (AddSucc _ _ Hq ad0))
  (let ((erased ad1)) (add-succ-right d1 j Hq ad0))
  (let ((erased cl)) (lt-trans c (Succ c) u62-modulus (lt-succ c) (lt-trans _ _ _ ml lbg)))
  (let ((many q) (erased k3) (erased r) (erased mm) (erased dq) (erased rl) (erased _)) (u62-div c (Succ (Succ (Succ (Zero)))) cl three-lt (LtZ _)))
  (let-match erased (kid-div m1 q c k3 r e km mm dq rl) (Refl _ _))
  (let ((erased gf1) (unique ga1) (erased lg1) (erased mk1) (erased w1)) (notail $ mark-up H lenG gf ga lg lbg tg g gb q d1 (Succ j) pre1 hm1 le1 ad1))
  (let ((erased gf2) (unique ga2) (erased u) (erased lg2)) (put-fl gf1 ga1 lenG lg1 m ml g gb))
  (let ((erased w2)) (WgCons gf1 gf1 gf2 g m (WgNil gf1 g) u))
  (values gf2 ga2 lg2 (MkdCons gf2 g m e pre1 hm (fupd-ent gf1 gf2 m g u) (mkd-wr gf1 gf2 g pre1 mk1 w2)) (wr-cat gf gf1 gf2 g w1 w2)))

(def-fns _ $ (many kill-all : (erased (Nat) H len lenL lenG) (erased (Ctree) keep) (erased (List (U8)) ls0 ls) (erased (List Cnt) us) (erased (List (U8)) gf)
    (subterm many (List (Nat)) T)
    (erased (TPs ls0 H T) tp) (erased (AllLt T len) al) (many (Nat) off) (erased (Offs H off) of) (unique (Array Cnt us) a) (erased (Length Cnt us len) lu)
    (erased (Tally us H (Zero) keep) tk) (erased (CtCanon H keep) kc) (unique (Bytes ls) fa) (erased (Length (U8) ls lenL) ll) (erased (Lt lenL u62-modulus) lbl)
    (erased (TrieFit lenL H (Zero)) tf) (erased (Lv ls flag-live H (Zero) keep) lv) (unique (Bytes gf) ga) (erased (Length (U8) gf lenG) lg)
    (erased (Lt lenG u62-modulus) lbg) (erased (TrieFit lenG H (Zero)) tg) (many (Nat) g) (erased (Lt g u8-modulus) gb) ->
    (unique a is a2 at a) (erased (List (U8)) ls2) (unique (Bytes ls2) fa2 at fa) (erased (Length (U8) ls2 lenL) ll2) (erased (Lv ls2 flag-live H (Zero) keep) lv2)
    (erased (List (U8)) gf2) (unique (Bytes gf2) ga2 at ga) (erased (Length (U8) gf2 lenG) lg2) (erased (WrG gf g gf2) w) (erased (Mks gf2 g us H T) mk))
  (let-match many T (Cons _ i Tt) ((Nil _) (values a ls fa ll lv gf ga lg (WgNil gf g) (MksNil gf g us H))))
  (let-match erased tp (TPCons _ _ _ n _ nd tp1))
  (let-match erased al (ALCons _ _ _ il al1))
  (let ((erased ou) (erased xu)) (nth-exists _ us len i lu il))
  (let-match erased ou (MkCopy _ vu))
  (let-match erased vu (MkU62 k0 kb))
  (let ((many w) (unique a1)) (array-get _ us a i vu xu))
  (let-match many w (MkU62 k _))
  (let-match many k (Zero)
    ((Succ k1)
      (let ((unique a2) (erased ls2) (unique fa2) (erased ll2) (erased lv2) (erased gf2) (unique ga2) (erased lg2) (erased w2) (erased mk))
        (tail $ kill-all H len lenL lenG keep ls0 ls us gf Tt tp1 al1 off of a1 lu tk kc fa ll lbl tf lv ga lg lbg tg g gb))
      (values a2 ls2 fa2 ll2 lv2 gf2 ga2 lg2 w2 (MksLive gf2 g us H i k1 Tt (MkEnt us i (Succ k1) kb xu) mk))))
  (let-match erased nd (MkNd _ _ _ _ _ d lenN pre ri hi le ad _ lbn tfn))
  (let-match erased (add-fn d (Zero) H d ad (add-zero-right d)) (Refl _ _))
  (let ((many m)) (u62-add off i n (hidx-off pre n i d off hi ri le of) (lt-trans _ _ _ (tfit-lt lenN (Zero) n tfn) lbn)))
  (let ((erased am)) (trace-dead us H i keep pre tk kc ri le (MkEnt us i (Zero) kb xu)))
  (let ((erased ls1) (unique fa1) (erased ll1) (erased lv1)) (kill-up H lenL keep ls fa ll lbl tf kc lv m d (Zero) pre hi le ad am))
  (let ((erased gf1) (unique ga1) (erased lg1) (erased md) (erased w1)) (mark-up H lenG gf ga lg lbg tg g gb m d (Zero) pre hi le ad))
  (let ((unique a2) (erased ls2) (unique fa2) (erased ll2) (erased lv2) (erased gf2) (unique ga2) (erased lg2) (erased w2) (erased mk))
    (tail $ kill-all H len lenL lenG keep ls0 ls1 us gf1 Tt tp1 al1 off of a1 lu tk kc fa1 ll1 lbl tf lv1 ga1 lg1 lbg tg g gb))
  (values a2 ls2 fa2 ll2 lv2 gf2 ga2 lg2 (wr-cat gf gf1 gf2 g w1 w2) (MksDead gf2 g us H i pre Tt ri le (mkd-wr gf1 gf2 g pre md w2) mk)))

(def-fns _ $ (many srestrict : (many (Nat) h) (many (Sx) sx) (erased (Gtree) gtr) (erased (List (U8)) gts) (unique (Bytes gts) gq)
    (erased (Gm gts (Succ h) sx (GSG gtr)) mg) (erased (SxLive gts sx) glv) (erased (Ctree) ctu) (erased (Nat) len) (erased (Lt len u62-modulus) lb)
    (erased (List Cnt) us) (unique (Array Cnt us) a) (erased (Tally us (Succ h) (Zero) ctu) tb) (erased (Length Cnt us len) lu)
    (erased (List (U8)) ls) (unique (Bytes ls) fa) (erased (Room ls (Succ h)) rm) (erased (Lv ls flag-live (Succ h) (Zero) ctu) lv)
    (many (Nat) off) (erased (Offs (Succ h) off) of) (erased (List (U8)) gf) (unique (Bytes gf) ga) (erased (Room gf (Succ h)) rg) (many (Nat) gen)
    (erased (Lt gen u8-modulus) gb) (erased (List Cnt) ws) (unique (Array Cnt ws) g) (erased (Tally ws (Succ h) (Zero) (CEmpty)) wz) (erased (Length Cnt ws len) lw) ->
    (erased (Ctree) keep gone) (erased (CRes h ctu (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)) keep gone) c)
    (erased (CtH (Succ h) keep) hk) (erased (CtH (Succ h) gone) hg) (many (KeepE keep) e)
    (erased (List Cnt) us2) (unique (Array Cnt us2) a2 at a) (erased (Tally us2 (Succ h) (Zero) keep) tk) (erased (Length Cnt us2 len) lu2)
    (erased (Fit us2) fk) (erased (List (U8)) ls2) (unique (Bytes ls2) fa2 at fa) (erased (Room ls2 (Succ h)) rm2) (erased (Lv ls2 flag-live (Succ h) (Zero) keep) lv2)
    (erased (List Cnt) ws2) (unique (Array Cnt ws2) g2 at g) (erased (Tally ws2 (Succ h) (Zero) gone) tg) (erased (Length Cnt ws2 len) lw2)
    (erased (Fit ws2) fg) (many (List (Nat)) T) (erased (AllLt T len) al) (erased (ZoT ws2 T (Succ h) (Zero)) zt) (erased (List (U8)) gf2)
    (unique (Bytes gf2) ga2 at ga) (erased (Room gf2 (Succ h)) rg2) (erased (Lv gf2 gen (Succ h) (Zero) gone) lvg) (unique gq is gq2 at gq))
  (let ((erased r)) (Cons RG (MkRx (Gtree) (BS0) gtr) (Nil RG)))
  (let ((erased H)) (Succ h))
  (let ((erased ct)) (tally-canon us H (Zero) ctu tb))
  (let ((erased hc)) (canon-h H ctu ct))
  (let ((erased u0) (erased ut) (erased _)) (ut-of h ctu hc))
  (let ((erased _) (erased gone0) (erased keep0) (erased _) (erased c0) (erased _) (erased _))
    (ctree-restrict-u h u0 ctu ut r (RxCons (Gtree) (BS0) gtr (Nil RG) (RxNil (Gtree)))))
  (let ((erased keep) (erased c1) (erased kc)) (cres-canon h ctu keep0 gone0 r c0 ct))
  (let ((erased gone) (erased c) (erased gc) (erased go)) (gone-tight h ctu keep gone0 r c1 ct))
  (let-match erased rm (MkRoom _ _ lenL ll lbl tf))
  (let-match erased rg (MkRoom _ _ lenG lg lbg tg))
  (let ((erased pz)) (MkPz us ls H H (Zero) (Zero) ctu tb lv (MkNd ls H H (Zero) (Zero) (Zero) lenL (Nil _) (RINil) (HxNil) (LengthNil _) (AddZero H) ll lbl tf)))
  (let ((erased Ps0)) (Cons _ (MkPr us ls H H (Zero) (Zero) (BS0) ctu pz) (Nil _)))
  (let ((unique fa1) (unique gq1) (erased us1) (erased ws1) (unique a1) (unique g1) (many T) (erased gl) (erased w))
    (swalk us ls H len lu lb h gts gq sx (GSG gtr) mg glv Ps0 (PsCons us ls H H (Zero) (Zero) (BS0) ctu pz (Nil _) (PsNil us ls H H)) fa us ws a g
      (Nil _) (MkGlob ls H len us ws (Nil _) lu lw (ALNil len) (TPNil ls H))))
  (let-match erased gl (MkGlob _ _ _ _ _ _ lu1 lw1 al tp))
  (let ((erased ws2) (unique a2) (unique g2) (erased lw2) (erased fx)) (fix-c len T al us1 ws1 a1 g1 lu1 lw1))
  (let ((erased dn)) (MkSDone h ctu keep gone gtr us ls ws us1 ws1 ws2 T pz wz w fx c hc go))
  (let ((erased pk) (erased pg) (erased zt)) (pw-both h us1 ws2 keep gone T dn H (Zero) (Zero) (Nil _) (RINil) (LengthNil _) (add-zero-right H)))
  (let ((erased tk)) (tally-of-pointwise us1 keep keep H (Zero) (Nil _) pk kc (AtNil keep)))
  (let ((unique a3) (erased ls2) (unique fa2) (erased ll2) (erased lv2) (erased gf2) (unique ga2) (erased lg2) (erased _) (erased mk))
    (kill-all H len lenL lenG keep ls ls us1 gf T tp al off of a2 lu1 tk kc fa1 ll lbl tf (lv-cres ls flag-live h (Zero) ctu keep gone r c lv) ga lg lbg tg gen gb))
  (let ((erased tgo)) (tally-of-pointwise ws2 gone gone H (Zero) (Nil _) pg gc (AtNil gone)))
  (let ((unique fa3) (erased v) (erased x) (many d)) (flag-get ls2 fa2 lenL ll2 (Zero) (tfit-lt lenL H (Zero) tf) flag-live flag-one-lt8))
  (let ((many e))
    (match many d (((KeepE keep) e))
      ((Equal _ _ _) (KLive keep))
      ((Unequal _ _ _ _ ap) (let-match erased (lv-ne ls2 flag-live H (Zero) v keep lv2 x ap) (Refl _ _)) (KEmpty))))
  (values keep gone c (canon-h H keep kc) (canon-h H gone gc) e us1 a3 tk lu1 (MkFit us1 len lu1 lb) ls2 fa3 (MkRoom ls2 H lenL ll2 lbl tf) lv2
    ws2 g2 tgo lw2 (MkFit ws2 len lw2 lb) T al zt gf2 ga2 (MkRoom gf2 H lenG lg2 lbg tg)
    (lv-marks h us1 ws2 gf2 keep gone gone T gen H (Zero) (Zero) (Zero) dn mk (Nil _) tgo (RINil) (HxNil) (LengthNil _) (add-zero-right H)) gq1))

(def-fns _ $ (erased tally-zeros : (erased (List Cnt) us ws) (erased (Nat) j p len) (erased (Ctree) t) (subterm erased (Tally us j p t) tb)
    (erased (Length Cnt us len) lu) (erased (Repeat Cnt len (MkCopy (U62) (MkU62 (Zero) u62-modulus-pos)) ws) rp) -> (erased (Tally ws j p (CEmpty)) r))
  (let-match erased tb (TaN _ j1 _ q t1 t2 t3 _ tq b1 b2 b3 _)
    ((TaL _ _ _ _ _ x _ _) (TaL ws p (Zero) u62-modulus-pos (CEmpty) (repeat-nth _ len p _ ws rp (nth-lt-length _ us p len _ x lu)) (RootE) (HE (Zero)))))
  (let ((erased e)) (CEmpty))
  (TaN ws j1 p q e e e e tq (tally-zeros us ws j1 q len t1 b1 lu rp) (tally-zeros us ws j1 (Succ q) len t2 b2 lu rp)
    (tally-zeros us ws j1 (Succ (Succ q)) len t3 b3 lu rp) (CnE)))

; What srestrict needs of its arrays, as sinit makes them from ctu.
(def-adts $ (SInit : ((Nat) h) ((Ctree) ctu) ((List Cnt) us) ((List Cnt) ws) -> Type)
  enum
  (many MkSInit : (erased (Nat) h) (erased (Ctree) ctu) (erased (List Cnt) us ws) (erased (Nat) len) (erased (Lt len u62-modulus) lb)
      (erased (Tally us (Succ h) (Zero) ctu) tb) (erased (Length Cnt us len) lu) (erased (Tally ws (Succ h) (Zero) (CEmpty)) wz)
      (erased (Length Cnt ws len) lw) -> (SInit h ctu us ws)))

(def-fns _ $ (many sinit : (many (Nat) h) (many (Ctree) ctu) (erased (CtH (Succ h) ctu) hc) ->
    (erased (List Cnt) us ws) (unique (Array Cnt us) a) (unique (Array Cnt ws) g) (many (Try (SInit h ctu us ws)) r))
  (let ((erased us) (unique a) (many r)) (ctree-tally (Succ h) ctu hc))
  (let ((many len) (erased lu) (unique a1)) (array-length _ us a))
  (let ((erased ws) (unique g) (erased rp)) (array-make (U62) len (MkU62 (Zero) u62-modulus-pos)))
  (let-match many r (TryOk _ pk) ((TryNo _) (values us ws a1 g (TryNo _))))
  (let-match erased pk (MkPacked _ _ _ tb f))
  (let-match erased f (MkFit _ len2 l2 lb))
  (let-match erased (length-fn _ us len len2 lu l2) (Refl _ _))
  (values us ws a1 g (TryOk _ (MkSInit h ctu us ws len lb tb lu (tally-zeros us ws (Succ h) (Zero) len ctu tb lu rp) (repeat-length _ len _ ws rp)))))
