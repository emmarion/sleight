; self/heap.sl -- the compile-time store: a value is stamped with its position in an erased ghost
; history, and refers to other values directly rather than through an address. The history makes
; position -> value a function (suffix-unique below), which is what lets the emitter name a value
; it has already written; at runtime a Store is the next stamp alone and a Ref is its target.
; Parametric in the block type, which takes the reference type as its parameter so that it never
; mentions the history. Nothing here is settled design.

(def-adts
  (Digit : -> Type
    enum
    (many D1 : -> (Digit))
    (many D2 : -> (Digit)))
  (Wrap : ((List $ Digit) ctx) ((Nat) inner) ((Nat) outer) -> Type
    enum
    (many WNil : (erased (Nat) x) -> (Wrap (Nil $ Digit) x x))
    (many W1 : (erased (List $ Digit) ctx) (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) y) (erased (Wrap ctx (Succ d) y) p) -> (Wrap (Cons (Digit) (D1) ctx) x y))
    (many W2 : (erased (List $ Digit) ctx) (erased (Nat) x) (erased (Nat) d) (erased (Double x d) dd) (erased (Nat) y) (erased (Wrap ctx (Succ (Succ d)) y) p) -> (Wrap (Cons (Digit) (D2) ctx) x y))))

; ---- lemmas over the prelude's Lt and Double, shared with core.sl's fact table

(def-fns _ $ erased lt-zero : (erased (Nat) a) (erased (Lt a (Zero)) p) -> (erased (False) f)
  (match erased p _ (absurd LtZ) (absurd LtS)))

(def-fns _ $ erased le-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a (Succ c)) r)
  (lt-le-trans a (Succ b) (Succ c) p (LtS b (Succ c) q)))

(def-fns _ $ erased add-shift : (erased (Nat) n) (erased (Nat) k) (erased (Nat) size) (subterm erased (Add n (Succ k) size) sum) -> (erased (Add (Succ n) k size) r)
  (match erased sum _
    ((AddZero b) (AddSucc (Zero) k k (AddZero k)))
    ((AddSucc a b c q) (AddSucc (Succ a) k c (add-shift a k c q)))))

(def-fns _ $ erased lt-irrefl : (erased (Nat) a) (erased (Lt a a) p) -> (erased (False) f)
  (lt-asym a a p (lt-succ a)))

(def-fns _ $ erased double-lt-inv : (erased (Nat) m) (erased (Nat) d) (erased (Nat) l) (erased (Nat) s) (subterm erased (Double m d) p) (erased (Double l s) q) (erased (Lt d s) lt) -> (erased (Lt m l) r)
  (match erased p _
    ((D0)
      (match erased q _
        (absurd (D0) (lt-zero d lt))
        ((DS l1 s1 q1) (LtZ l1))))
    ((DS m1 d1 p1)
      (match erased q _
        (absurd (D0) (lt-zero d lt))
        ((DS l1 s1 q1)
          (match erased lt _
            ((LtS x y lt1)
              (match erased lt1 _
                ((LtS x2 y2 lt2) (LtS m1 l1 (double-lt-inv m1 d1 l1 s1 p1 q1 lt2)))))))))))

(def-fns _ $ erased wrap-fn : (erased (List $ Digit) ctx) (erased (Nat) a) (erased (Nat) x) (erased (Nat) y) (subterm erased (Wrap ctx a x) p) (erased (Wrap ctx a y) q) -> (erased (Eq (Nat) x y) e)
  (match erased p _
    ((WNil z) (match erased q _ ((WNil z2) (Refl (Nat) x))))
    ((W1 c1 a1 d1 dd1 x1 p1)
      (match erased q _
        ((W1 c2 a2 d2 dd2 y1 q1)
          (match erased (double-fn a d1 d2 dd1 dd2) _ ((Refl t r) (wrap-fn c1 (Succ d1) x y p1 q1))))))
    ((W2 c1 a1 d1 dd1 x1 p1)
      (match erased q _
        ((W2 c2 a2 d2 dd2 y1 q1)
          (match erased (double-fn a d1 d2 dd1 dd2) _ ((Refl t r) (wrap-fn c1 (Succ (Succ d1)) x y p1 q1))))))))

; ---- the ghost history: an erased list of every value allocated so far, newest first

(def-adts
  ; [B] the block type at a value; [l] the allocations before a point; [s] the ones before a
  ; value the reference names, so a Ref is valid in l and its target was made at s.
  (Hist : ((TyCtor (Type R) -> Type) B) -> Type
    enum
    (many HEmpty : (erased (TyCtor (Type R) -> Type) B) -> (Hist B))
    (many HAdd : (erased (TyCtor (Type R) -> Type) B) (many (Hist B) rest) (many (Value B rest) v) -> (Hist B)))
  (Value : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type
    enum
    (many MkValue : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (many (Nat) pos) (erased (Len B l pos) lp) (many (B (Ref B l)) body) -> (Value B l)))
  (Len : ((TyCtor (Type R) -> Type) B) ((Hist B) l) ((Nat) n) -> Type
    enum
    (many LenNil : (erased (TyCtor (Type R) -> Type) B) -> (Len B (HEmpty B) (Zero)))
    (many LenAdd : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) rest) (erased (Value B rest) v) (erased (Nat) n) (erased (Len B rest n) p) -> (Len B (HAdd B rest v) (Succ n))))
  (Suffix : ((TyCtor (Type R) -> Type) B) ((Hist B) l) ((Hist B) s) -> Type
    enum
    (many SfHere : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) h) -> (Suffix B h h))
    (many SfThere : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) rest) (erased (Value B rest) w) (erased (Hist B) s) (erased (Suffix B rest s) p) -> (Suffix B (HAdd B rest w) s)))
  (Ref : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type
    enum newtype
    (many MkRef : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Hist B) s) (many (Value B s) v) (erased (Suffix B l (HAdd B s v)) p) -> (Ref B l))))

(def-adts $ Store : ((TyCtor (Type R) -> Type) B) ((Hist B) l) -> Type
  enum newtype
  (many MkStore : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (many (Nat) next) (erased (Len B l next) ln) -> (Store B l)))

; ---- a position names one value: the history has one suffix of each length, and a value sits at
; the head of the suffix it was allocated onto. Nothing calls these; they are the obligation.

(def-fns _ $ erased len-fn : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Nat) n) (erased (Nat) m)
    (subterm erased (Len B l n) p) (erased (Len B l m) q) -> (erased (Eq (Nat) n m) e)
  (match erased p _
    ((LenNil tb) (match erased q _ ((LenNil tb2) (Refl (Nat) (Zero)))))
    ((LenAdd tb r1 v1 n1 p1)
      (match erased q _
        ((LenAdd tb2 r2 v2 m1 q1)
          (match erased (len-fn _ r1 n1 m1 p1 q1) _ ((Refl t x) (Refl (Nat) (Succ n1)))))))))

(def-fns _ $ erased suffix-len : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Hist B) s)
    (subterm erased (Suffix B l s) p) (erased (Nat) n) (erased (Len B s n) ls) (erased (Nat) m) (erased (Len B l m) ll) ->
    (erased (Lt n (Succ m)) r)
  (match erased p _
    ((SfHere tb h) (match erased (len-fn _ l n m ls ll) _ ((Refl t x) (lt-succ n))))
    ((SfThere tb rest w s1 p1)
      (match erased ll _
        ((LenAdd tb2 r2 v2 m1 ll1) (lt-weaken n (Succ m1) (suffix-len _ rest s1 p1 n ls m1 ll1)))))))

(def-fns _ $ erased suffix-unique : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Hist B) s1)
    (erased (Hist B) s2) (erased (Nat) n) (subterm erased (Suffix B l s1) p1) (erased (Suffix B l s2) p2)
    (erased (Len B s1 n) l1) (erased (Len B s2 n) l2) -> (erased (Eq (Hist B) s1 s2) e)
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

(def-fns _ $ erased ref-unique : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l)
    (erased (Hist B) s1) (erased (Value B s1) v1) (erased (Suffix B l (HAdd B s1 v1)) p1)
    (erased (Hist B) s2) (erased (Value B s2) v2) (erased (Suffix B l (HAdd B s2 v2)) p2)
    (erased (Nat) n) (erased (Len B s1 n) n1) (erased (Len B s2 n) n2) ->
    (erased (Eq (Hist B) (HAdd B s1 v1) (HAdd B s2 v2)) e)
  (suffix-unique _ l (HAdd B s1 v1) (HAdd B s2 v2) (Succ n) p1 p2 (LenAdd _ s1 v1 n n1) (LenAdd _ s2 v2 n n2)))

; ---- the operations

(def-fns _ $ erased suffix-trans : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) a) (erased (Hist B) b)
    (erased (Hist B) c) (subterm erased (Suffix B a b) p) (erased (Suffix B b c) q) -> (erased (Suffix B a c) r)
  (match erased p _
    ((SfHere tb h) q)
    ((SfThere tb rest w s p1) (SfThere _ rest w c (suffix-trans _ rest b c p1 q)))))

(def-fns _ $ erased suffix-one : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) s) (erased (Value B s) v) ->
    (erased (Suffix B (HAdd B s v) s) r)
  (SfThere _ s v s (SfHere _ s)))

(def-fns _ $ erased empty-suffix : (erased (TyCtor (Type R) -> Type) B) (subterm erased (Hist B) l) ->
    (erased (Suffix B l (HEmpty B)) r)
  (match erased l _
    ((HEmpty tb) (SfHere _ _))
    ((HAdd tb rest v) (SfThere _ rest v (HEmpty B) (empty-suffix _ rest)))))

(def-fns _ $ many store-empty : (erased (TyCtor (Type R) -> Type) B) -> (many (Store B (HEmpty B)) s)
  (MkStore _ _ (Zero) (LenNil _)))

(def-fns _ $ many alloc : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (many (Store B l) st)
    (many (B (Ref B l)) body) ->
    (erased (Hist B) l2) (many (Store B l2) st2) (erased (Suffix B l2 l) sf) (many (Ref B l2) at)
  (match many st _
    ((MkStore tb l0 next ln)
      (let (many (Value B l) v) (MkValue _ _ next ln body))
      (values (HAdd _ l v) (MkStore _ _ (Succ next) (LenAdd _ l v next ln)) (suffix-one _ l v)
              (MkRef _ _ l v (SfHere _ (HAdd _ l v)))))))

(def-fns _ $ erased ref-suffix : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (erased (Hist B) s)
    (erased (Value B s) v) (erased (Suffix B l (HAdd B s v)) p) -> (erased (Suffix B l s) r)
  (suffix-trans _ l (HAdd _ s v) s p (suffix-one _ s v)))

(def-fns _ $ many ref-pos : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) l) (many (Ref B l) r) -> (many (Nat) p)
  (match many r _ ((MkRef tb l0 s v p) (match many v _ ((MkValue tb2 s0 pos lp body) pos)))))

; ---- growth: an erased function builds the proof and the call site coerces, so widening runs no code

(def-fns _ $ erased ref-widen : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (erased (Ref B b) r) -> (erased (Ref B c) r2) (erased (Coercible (Ref B b) r (Ref B c) r2) p)
  (match erased r _
    ((MkRef tb b0 s v p)
      (let (erased p2) (suffix-trans _ c b (HAdd _ s v) le p))
      (values (MkRef _ _ s v p2) (coercible-ctor MkRef B B b c s s (coercible-refl v) p p2)))))

(def-fns _ $ erased refs-widen : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (subterm erased (List $ Ref B b) xs) ->
    (erased (List $ Ref B c) ys) (erased (Coercible (List $ Ref B b) xs (List $ Ref B c) ys) p)
  (match erased xs _
    ((Nil t) (values (Nil _) (coercible-ctor Nil (Ref B b) (Ref B c))))
    ((Cons t x rest)
      (let (erased x2) (erased px) (ref-widen _ b c le x))
      (let (erased rest2) (erased pr) (refs-widen _ b c le rest))
      (values (Cons _ x2 rest2) (coercible-ctor Cons (Ref B b) (Ref B c) px pr)))))

(def-fns _ $ erased refs-widen-lk : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (erased (List $ Nat) f) (subterm erased (List $ Ref B b) xs) (erased (Lockstep (Nat) (Ref B b) f xs) lk) ->
    (erased (List $ Ref B c) ys) (erased (Coercible (List $ Ref B b) xs (List $ Ref B c) ys) p) (erased (Lockstep (Nat) (Ref B c) f ys) lk2)
  (match erased xs _
    ((Nil t) (match erased lk _ ((LsNil ta tb) (values (Nil _) (coercible-ctor Nil (Ref B b) (Ref B c)) (LsNil _ _)))))
    ((Cons t x rest)
      (match erased lk _
        ((LsCons ta tb x0 y0 xs0 ys0 lk1)
          (let (erased x2) (erased px) (ref-widen _ b c le x))
          (let (erased rest2) (erased pr) (erased lk2) (refs-widen-lk _ b c le xs0 rest lk1))
          (values (Cons _ x2 rest2) (coercible-ctor Cons (Ref B b) (Ref B c) px pr) (LsCons _ _ x0 x2 xs0 rest2 lk2)))))))

(def-fns _ $ erased maybe-widen : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (erased (Maybe $ Ref B b) m) ->
    (erased (Maybe $ Ref B c) m2) (erased (Coercible (Maybe $ Ref B b) m (Maybe $ Ref B c) m2) p)
  (match erased m _
    ((None t) (values (None _) (coercible-ctor None (Ref B b) (Ref B c))))
    ((Some t x)
      (let (erased x2) (erased px) (ref-widen _ b c le x))
      (values (Some _ x2) (coercible-ctor Some (Ref B b) (Ref B c) px)))))

(def-fns _ $ erased idmap-widen : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (subterm erased (IdMap $ Ref B b) m) ->
    (erased (IdMap $ Ref B c) m2) (erased (Coercible (IdMap $ Ref B b) m (IdMap $ Ref B c) m2) p)
  (match erased m _
    ((MEmpty t) (values (MEmpty _) (coercible-ctor MEmpty (Ref B b) (Ref B c))))
    ((MNode t here one two)
      (let (erased here2) (erased ph) (maybe-widen _ b c le here))
      (let (erased one2) (erased p1) (idmap-widen _ b c le one))
      (let (erased two2) (erased p2) (idmap-widen _ b c le two))
      (values (MNode _ here2 one2 two2) (coercible-ctor MNode (Ref B b) (Ref B c) ph p1 p2)))))

; TEMPORARY: the weaken wrappers, to be removed in favour of an inline coerce at each call site.

(def-fns _ $ many ref-weaken : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (many (Ref B b) r) -> (many (Ref B c) r2)
  (let (erased r2) (erased p) (ref-widen _ b c le r))
  (coerce r p))

(def-fns _ $ many refs-weaken : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (many (List $ Ref B b) xs) -> (many (List $ Ref B c) r)
  (let (erased ys) (erased p) (refs-widen _ b c le xs))
  (coerce xs p))

(def-fns _ $ many idmap-weaken : (erased (TyCtor (Type R) -> Type) B) (erased (Hist B) b) (erased (Hist B) c)
    (erased (Suffix B c b) le) (many (IdMap $ Ref B b) m) -> (many (IdMap $ Ref B c) r)
  (let (erased m2) (erased p) (idmap-widen _ b c le m))
  (coerce m p))
