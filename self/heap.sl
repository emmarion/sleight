; self/heap.sl -- the compile-time store: a value is stamped with its position in an erased ghost
; history, and refers to other values directly rather than through an address. The history makes
; position -> value a function (suffix-unique below), which is what lets the emitter name a value
; it has already written.
; Parametric in the block type, which takes the reference type as its parameter so that it never
; mentions the history. Nothing here is settled design.

(def-adts
  ((Digit : -> Type)
    enum
    (many D1 : -> (Digit))
    (many D2 : -> (Digit)))
  ((Wrap : ((List $ Digit) ctx) ((Nat) inner) ((Nat) outer) -> Type)
    enum
    (many WNil : (erased (Nat) x) -> (Wrap (Nil $ Digit) x x))
    (many W1 : (erased (List $ Digit) ctx) (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) y) (erased (Wrap ctx (Succ d) y) p) -> (Wrap (Cons (Digit) (D1) ctx) x y))
    (many W2 : (erased (List $ Digit) ctx) (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) y) (erased (Wrap ctx (Succ (Succ d)) y) p) -> (Wrap (Cons (Digit) (D2) ctx) x y))))

; ---- lemmas over the prelude's Lt and Double

(def-fns _ $ (erased add-shift : (erased (Nat) n) (erased (Nat) k) (erased (Nat) size) (subterm erased (Add n (Succ k) size) sum) -> (erased (Add (Succ n) k size) r))
  (match erased sum _
    ((AddZero b) (AddSucc (Zero) k k (AddZero k)))
    ((AddSucc a b c q) (AddSucc (Succ a) k c (add-shift a k c q)))))

(def-fns _ $ (erased lt-irrefl : (erased (Nat) a) (erased (Lt a a) p) -> (erased (False) f))
  (lt-asym a a p (lt-succ a)))

(def-fns _ $ (erased wrap-fn : (erased (List $ Digit) ctx) (erased (Nat) a) (erased (Nat) x) (erased (Nat) y) (subterm erased (Wrap ctx a x) p) (erased (Wrap ctx a y) q) -> (erased (Eq (Nat) x y) e))
  (match erased p _
    ((WNil z)
      (let-match erased q (WNil z2))
      (Refl (Nat) x))
    ((W1 c1 a1 d1 dd1 x1 p1)
      (let-match erased q (W1 c2 a2 d2 dd2 y1 q1))
      (match erased (double-fn a d1 d2 dd1 dd2) _ ((Refl t r) (wrap-fn c1 (Succ d1) x y p1 q1))))
    ((W2 c1 a1 d1 dd1 x1 p1)
      (let-match erased q (W2 c2 a2 d2 dd2 y1 q1))
      (match erased (double-fn a d1 d2 dd1 dd2) _ ((Refl t r) (wrap-fn c1 (Succ (Succ d1)) x y p1 q1))))))

; ---- the ghost history: an erased list of every value allocated so far, newest first

(def-adts
  ; [B] the block type at a value; [l] the allocations before a point; [s] the ones before a
  ; value the reference names, so a Ref is valid in l and its target was made at s.
  ((Hist : ((TyCtor (Type R) -> Type) B) -> Type)
    enum
    (many HEmpty : (erased (TyCtor (Type R) -> Type) B) -> (Hist B))
    (many HAdd : (erased (TyCtor (Type R) -> Type) B) (many (Hist B) rest) (many (Value B rest) v) -> (Hist B)))
  ((Value : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type)
    enum
    (many MkValue : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (many (Nat) pos) (erased (Len B l pos) lp) (many (B (Ref B l)) body) -> (Value B l)))
  ((Len : ((TyCtor (Type R) -> Type) B) ((Hist B) l) ((Nat) n) -> Type)
    enum
    (many LenNil : (erased (TyCtor (Type R) -> Type) B) -> (Len B (HEmpty B) (Zero)))
    (many LenAdd : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) rest) (erased (Value B rest) v) (erased (Nat) n) (erased (Len B rest n) p) -> (Len B (HAdd B rest v) (Succ n))))
  ((Suffix : ((TyCtor (Type R) -> Type) B) ((Hist B) l) ((Hist B) s) -> Type)
    enum
    (many SfHere : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) h) -> (Suffix B h h))
    (many SfThere : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) rest) (erased (Value B rest) w) (erased (Hist B) s) (erased (Suffix B rest s) p) -> (Suffix B (HAdd B rest w) s)))
  ((Ref : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type)
    enum newtype
    (many MkRef : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Hist B) s) (many (Value B s) v) (erased (Suffix B l (HAdd B s v)) p) -> (Ref B l))))

(def-adts
  ((StoredBody : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type)
    enum newtype
    (many MkStoredBody : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l)
      (erased (Hist B) s) (many (B (Ref B s)) body) (erased (Suffix B l s) sf) -> (StoredBody B l)))
  ((Store : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type)
    enum
    (many MkStore : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l)
      (many (Nat) next) (erased (Len B l next) ln)
      (many (IdMap $ StoredBody B l) writes) -> (Store B l))))

; ---- a position names one value: the history has one suffix of each length, and a value sits at
; the head of the suffix it was allocated onto. Nothing calls these; they are the obligation.

(def-fns _ $ (erased len-fn : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Nat) n) (erased (Nat) m)
    (subterm erased (Len B l n) p) (erased (Len B l m) q) -> (erased (Eq (Nat) n m) e))
  (match erased p _
    ((LenNil tb)
      (let-match erased q (LenNil tb2))
      (Refl (Nat) (Zero)))
    ((LenAdd tb r1 v1 n1 p1)
      (let-match erased q (LenAdd tb2 r2 v2 m1 q1))
      (match erased (len-fn _ r1 n1 m1 p1 q1) _ ((Refl t x) (Refl (Nat) (Succ n1)))))))

(def-fns _ $ (erased suffix-len : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Hist B) s)
    (subterm erased (Suffix B l s) p) (erased (Nat) n) (erased (Len B s n) ls) (erased (Nat) m) (erased (Len B l m) ll) ->
    (erased (Lt n (Succ m)) r))
  (match erased p _
    ((SfHere tb h) (match erased (len-fn _ l n m ls ll) _ ((Refl t x) (lt-succ n))))
    ((SfThere tb rest w s1 p1)
      (let-match erased ll (LenAdd tb2 r2 v2 m1 ll1))
      (lt-weaken n (Succ m1) (suffix-len _ rest s1 p1 n ls m1 ll1)))))

(def-fns _ $ (erased suffix-unique : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Hist B) s1)
    (erased (Hist B) s2) (erased (Nat) n) (subterm erased (Suffix B l s1) p1) (erased (Suffix B l s2) p2)
    (erased (Len B s1 n) l1) (erased (Len B s2 n) l2) -> (erased (Eq (Hist B) s1 s2) e))
  (match erased p1 _
    ((SfHere tb h)
      (match erased p2 _
        ((SfHere tb2 h2) (Refl (Hist B) s1))
        (absurd (SfThere tb2 rest w s0 q)
          (match erased l1 (((False) f))
            ((LenAdd tb3 r3 v3 n0 l1b) (lt-irrefl n (suffix-len _ rest s2 q n l2 n0 l1b)))))))
    ((SfThere tb rest w s0 q)
      (match erased p2 _
        (absurd (SfHere tb2 h2)
          (match erased l2 (((False) f))
            ((LenAdd tb3 r3 v3 n0 l2b) (lt-irrefl n (suffix-len _ rest s1 q n l1 n0 l2b)))))
        ((SfThere tb2 rest2 w2 s02 q2) (suffix-unique _ rest s1 s2 n q q2 l1 l2))))))

(def-fns _ $ (erased ref-unique : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l)
    (erased (Hist B) s1) (erased (Value B s1) v1) (erased (Suffix B l (HAdd B s1 v1)) p1)
    (erased (Hist B) s2) (erased (Value B s2) v2) (erased (Suffix B l (HAdd B s2 v2)) p2)
    (erased (Nat) n) (erased (Len B s1 n) n1) (erased (Len B s2 n) n2) ->
    (erased (Eq (Hist B) (HAdd B s1 v1) (HAdd B s2 v2)) e))
  (suffix-unique _ l (HAdd B s1 v1) (HAdd B s2 v2) (Succ n) p1 p2 (LenAdd _ s1 v1 n n1) (LenAdd _ s2 v2 n n2)))

; ---- the operations

(def-fns _ $ (erased suffix-trans : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) a) (erased (Hist B) b)
    (erased (Hist B) c) (subterm erased (Suffix B a b) p) (erased (Suffix B b c) q) -> (erased (Suffix B a c) r))
  (match erased p _
    ((SfHere tb h) q)
    ((SfThere tb rest w s p1) (SfThere _ rest w c (suffix-trans _ rest b c p1 q)))))

(def-fns _ $ (erased suffix-one : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) s) (erased (Value B s) v) ->
    (erased (Suffix B (HAdd B s v) s) r))
  (SfThere _ s v s (SfHere _ s)))

(def-fns _ $ (erased empty-suffix : (erased (TyCtor (Type R) -> Type) B) (subterm erased (Hist B) l) ->
    (erased (Suffix B l (HEmpty B)) r))
  (match erased l _
    ((HEmpty tb) (SfHere _ _))
    ((HAdd tb rest v) (SfThere _ rest v (HEmpty B) (empty-suffix _ rest)))))

(def-fns _ $ (erased stored-body-widen : (erased (TyCtor (Type R) -> Type) B)
    (erased (Hist B) b) (erased (Hist B) c) (erased (Suffix B c b) le)
    (erased (StoredBody B b) v) -> (erased (StoredBody B c) w)
    (erased (Coercible (Shared) (StoredBody B b) v (Shared) (StoredBody B c) w) p))
  (match erased v _
    ((MkStoredBody tb b0 s body sf)
      (let ((erased sf2)) (suffix-trans _ c b s le sf))
      (values (MkStoredBody _ _ s body sf2)
        (coercible-ctor (Shared) MkStoredBody B B b c s s (coercible-refl (Shared) body) sf sf2)))))

(def-fns _ $ (erased stored-maybe-widen : (erased (TyCtor (Type R) -> Type) B)
    (erased (Hist B) b) (erased (Hist B) c) (erased (Suffix B c b) le)
    (erased (Maybe $ StoredBody B b) v) -> (erased (Maybe $ StoredBody B c) w)
    (erased (Coercible (Shared) (Maybe $ StoredBody B b) v (Shared) (Maybe $ StoredBody B c) w) p))
  (match erased v _
    ((None t) (values (None _) (coercible-ctor (Shared) None (StoredBody B b) (StoredBody B c))))
    ((Some t x)
      (let ((erased x2) (erased px)) (stored-body-widen _ b c le x))
      (values (Some _ x2) (coercible-ctor (Shared) Some (StoredBody B b) (StoredBody B c) px)))))

(def-fns _ $ (erased stored-map-widen : (erased (TyCtor (Type R) -> Type) B)
    (erased (Hist B) b) (erased (Hist B) c) (erased (Suffix B c b) le)
    (subterm erased (IdMap $ StoredBody B b) v) -> (erased (IdMap $ StoredBody B c) w)
    (erased (Coercible (Shared) (IdMap $ StoredBody B b) v (Shared) (IdMap $ StoredBody B c) w) p))
  (match erased v _
    ((MEmpty t) (values (MEmpty _) (coercible-ctor (Shared) MEmpty (StoredBody B b) (StoredBody B c))))
    ((MNode t here one two)
      (let ((erased h2) (erased ph)) (stored-maybe-widen _ b c le here))
      (let ((erased o2) (erased po)) (stored-map-widen _ b c le one))
      (let ((erased t2) (erased pt)) (stored-map-widen _ b c le two))
      (values (MNode _ h2 o2 t2)
        (coercible-ctor (Shared) MNode (StoredBody B b) (StoredBody B c) ph po pt)))))

(def-fns _ $ (many store-empty : (erased (TyCtor (Type R) -> Type) B) -> (many (Store B (HEmpty B)) s))
  (MkStore _ _ (Zero) (LenNil _) (MEmpty _)))

(def-fns _ $ (many alloc : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (many (Store B l) st)
    (many (B (Ref B l)) body) ->
    (erased (Hist B) l2) (many (Store B l2) st2) (erased (Suffix B l2 l) sf) (many (Ref B l2) at))
  (match many st _
    ((MkStore tb l0 next ln writes)
      (let ((many (Value B l) v)) (MkValue _ _ next ln body))
      (let ((erased writes2) (erased pw)) (stored-map-widen _ l (HAdd _ l v) (suffix-one _ l v) writes))
      (values (HAdd _ l v) (MkStore _ _ (Succ next) (LenAdd _ l v next ln) (coerce writes pw)) (suffix-one _ l v)
              (MkRef _ _ l v (SfHere _ (HAdd _ l v)))))))

(def-fns _ $ (erased ref-suffix : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Hist B) s)
    (erased (Value B s) v) (erased (Suffix B l (HAdd B s v)) p) -> (erased (Suffix B l s) r))
  (suffix-trans _ l (HAdd _ s v) s p (suffix-one _ s v)))

; a reference's stamp, with the proof that it sits below the store's next stamp
(def-fns _ $ (many ref-key : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Nat) bound)
    (erased (Len B l bound) lb) (many (Ref B l) r) -> (many (Nat) k) (erased (Lt k bound) lt))
  (match many r _
    ((MkRef tb l0 s v p)
      (match many v _
        ((MkValue tb2 s0 pos lp body)
          (values pos (lt-succ-inv pos bound
            (suffix-len _ l (HAdd _ s v) p (Succ pos) (LenAdd _ s v pos lp) bound lb))))))))

(def-fns _ $ (many ref-pos : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (many (Ref B l) r) -> (many (Nat) p))
  (match many r _ ((MkRef tb l0 s v p) (match many v _ ((MkValue tb2 s0 pos lp body) pos)))))

(def-fns _ $ (many store-read : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l)
    (many (Store B l) st) (many (Ref B l) r) ->
    (erased (Hist B) s) (many (B (Ref B s)) body) (erased (Suffix B l s) sf))
  (let-match many st (MkStore _ _ next ln writes))
  (match many (idmap-get _ (ref-pos _ _ r) writes) _
    ((Hit t k m v p)
      (let-match many v (MkStoredBody _ _ s body sf))
      (values s body sf))
    ((Miss t k m p)
      (let-match many r (MkRef _ _ s v rp))
      (let-match many v (MkValue _ _ pos lp body))
      (values s body (ref-suffix _ _ s v rp)))))

(def-fns _ $ (many store-write : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l)
    (many (Store B l) st) (many (Ref B l) r) (many (B (Ref B l)) body) -> (many (Store B l) st2))
  (let-match many st (MkStore _ _ next ln writes))
  (MkStore _ _ next ln (idmap-set _ (ref-pos _ _ r) (MkStoredBody _ _ l body (SfHere _ l)) writes)))

; ---- growth: an erased function builds the proof and the call site coerces, so widening runs no code

(def-fns _ $ (erased ref-widen : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (erased (Ref B b) r) -> (erased (Ref B c) r2) (erased (Coercible (Shared) (Ref B b) r (Shared) (Ref B c) r2) p))
  (match erased r _
    ((MkRef tb b0 s v p)
      (let ((erased p2)) (suffix-trans _ c b (HAdd _ s v) le p))
      (values (MkRef _ _ s v p2) (coercible-ctor (Shared) MkRef B B b c s s (coercible-refl (Shared) v) p p2)))))

(def-fns _ $ (erased refs-widen : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (subterm erased (List $ Ref B b) xs) ->
    (erased (List $ Ref B c) ys) (erased (Coercible (Shared) (List $ Ref B b) xs (Shared) (List $ Ref B c) ys) p))
  (match erased xs _
    ((Nil t) (values (Nil _) (coercible-ctor (Shared) Nil (Ref B b) (Ref B c))))
    ((Cons t x rest)
      (let ((erased x2) (erased px)) (ref-widen _ b c le x))
      (let ((erased rest2) (erased pr)) (refs-widen _ b c le rest))
      (values (Cons _ x2 rest2) (coercible-ctor (Shared) Cons (Ref B b) (Ref B c) px pr)))))

(def-fns _ $ (erased refs-widen-lk : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (erased (List $ Nat) f) (subterm erased (List $ Ref B b) xs) (erased (Lockstep (Nat) (Ref B b) f xs) lk) ->
    (erased (List $ Ref B c) ys) (erased (Coercible (Shared) (List $ Ref B b) xs (Shared) (List $ Ref B c) ys) p) (erased (Lockstep (Nat) (Ref B c) f ys) lk2))
  (match erased xs _
    ((Nil t)
      (let-match erased lk (LsNil ta tb))
      (values (Nil _) (coercible-ctor (Shared) Nil (Ref B b) (Ref B c)) (LsNil _ _)))
    ((Cons t x rest)
      (let-match erased lk (LsCons ta tb x0 y0 xs0 ys0 lk1))
      (let ((erased x2) (erased px)) (ref-widen _ b c le x))
      (let ((erased rest2) (erased pr) (erased lk2)) (refs-widen-lk _ b c le xs0 rest lk1))
      (values (Cons _ x2 rest2) (coercible-ctor (Shared) Cons (Ref B b) (Ref B c) px pr) (LsCons _ _ x0 x2 xs0 rest2 lk2)))))

(def-fns _ $ (erased maybe-widen : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (erased (Maybe $ Ref B b) m) ->
    (erased (Maybe $ Ref B c) m2) (erased (Coercible (Shared) (Maybe $ Ref B b) m (Shared) (Maybe $ Ref B c) m2) p))
  (match erased m _
    ((None t) (values (None _) (coercible-ctor (Shared) None (Ref B b) (Ref B c))))
    ((Some t x)
      (let ((erased x2) (erased px)) (ref-widen _ b c le x))
      (values (Some _ x2) (coercible-ctor (Shared) Some (Ref B b) (Ref B c) px)))))

(def-fns _ $ (erased idmap-widen : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (subterm erased (IdMap $ Ref B b) m) ->
    (erased (IdMap $ Ref B c) m2) (erased (Coercible (Shared) (IdMap $ Ref B b) m (Shared) (IdMap $ Ref B c) m2) p))
  (match erased m _
    ((MEmpty t) (values (MEmpty _) (coercible-ctor (Shared) MEmpty (Ref B b) (Ref B c))))
    ((MNode t here one two)
      (let ((erased here2) (erased ph)) (maybe-widen _ b c le here))
      (let ((erased one2) (erased p1)) (idmap-widen _ b c le one))
      (let ((erased two2) (erased p2)) (idmap-widen _ b c le two))
      (values (MNode _ here2 one2 two2) (coercible-ctor (Shared) MNode (Ref B b) (Ref B c) ph p1 p2)))))
