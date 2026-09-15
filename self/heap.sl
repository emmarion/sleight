; self/heap.sl -- a store for the compile-time interpreter: addresses below a bound, and a Braun tree of blocks
; sized by its count, so that reading and appending are total by the size alone (the address 2k+1 sits in
; the one-child and 2k+2 in the two-child of the node at k, so the halves of an address are its path).
; Parametric in the block type, which core.sl supplies. Nothing here is settled design.

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

; ---- lemmas over the prelude's Lt and Double

(def-fns _ $ erased lt-zero : (erased (Nat) a) (erased (Lt a (Zero)) p) -> (erased (False) f)
  (match erased p _ (absurd LtZ) (absurd LtS)))

(def-fns _ $ erased lt-drop : (erased (Nat) d) (erased (Nat) s) (erased (Lt (Succ d) s) p) -> (erased (Lt d s) q)
  (match erased p _ ((LtS x y q) (lt-weaken d y q))))

(def-fns _ $ erased le-trans : (erased (Nat) a) (erased (Nat) b) (erased (Nat) c) (erased (Lt a (Succ b)) p) (erased (Lt b (Succ c)) q) -> (erased (Lt a (Succ c)) r)
  (lt-le-trans a (Succ b) (Succ c) p (LtS b (Succ c) q)))

(def-fns _ $ erased lt-of-add : (erased (Nat) n) (erased (Nat) k) (erased (Nat) size) (subterm erased (Add n (Succ k) size) sum) -> (erased (Lt n size) lt)
  (match erased sum _
    ((AddZero b) (LtZ k))
    ((AddSucc a b c q) (LtS a c (lt-of-add a k c q)))))

(def-fns _ $ erased add-shift : (erased (Nat) n) (erased (Nat) k) (erased (Nat) size) (subterm erased (Add n (Succ k) size) sum) -> (erased (Add (Succ n) k size) r)
  (match erased sum _
    ((AddZero b) (AddSucc (Zero) k k (AddZero k)))
    ((AddSucc a b c q) (AddSucc (Succ a) k c (add-shift a k c q)))))

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

(def-fns _ $ erased double-le-inv : (erased (Nat) m) (erased (Nat) d) (erased (Nat) r) (erased (Nat) s) (erased (Double m d) p) (erased (Double r s) q) (erased (Lt d (Succ s)) lt) -> (erased (Lt m (Succ r)) res)
  (double-lt-inv m d (Succ r) (Succ (Succ s)) p (DS r s q) (lt-weaken d (Succ s) lt)))

(def-adts $ Braun : ((Nat) l) ((Nat) r) -> Type
  enum
  (many BrEq : (erased (Nat) n) -> (Braun n n))
  (many BrOne : (erased (Nat) n) -> (Braun (Succ n) n)))

; The one-child of a node of size l + r + 1 holds the odd local indices: 2m+1 < l + r + 1 gives m < l.
(def-fns _ $ erased half-lt-one : (erased (Nat) m) (erased (Nat) d) (erased (Nat) l) (erased (Nat) r) (erased (Nat) s) (erased (Double m d) dd) (erased (Add l r s) sum) (erased (Braun l r) bal) (erased (Lt d s) lt) -> (erased (Lt m l) res)
  (match erased bal _
    ((BrEq n) (double-lt-inv m d n s dd (add-diag-double n s sum) lt))
    ((BrOne n)
      (match erased sum _
        ((AddSucc a1 b1 c1 q) (double-le-inv m d n c1 dd (add-diag-double n c1 q) lt))))))

; The two-child holds the even ones: 2m+2 < l + r + 1 gives m < r.
(def-fns _ $ erased half-lt-two : (erased (Nat) m) (erased (Nat) d) (erased (Nat) l) (erased (Nat) r) (erased (Nat) s) (erased (Double m d) dd) (erased (Add l r s) sum) (erased (Braun l r) bal) (erased (Lt (Succ d) s) lt) -> (erased (Lt m r) res)
  (match erased bal _
    ((BrEq n) (double-lt-inv m d n s dd (add-diag-double n s sum) (lt-drop d s lt)))
    ((BrOne n)
      (match erased sum _
        ((AddSucc a1 b1 c1 q)
          (match erased lt _
            ((LtS x y lt1) (double-lt-inv m d n c1 dd (add-diag-double n c1 q) lt1))))))))

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

; ---- addresses: a number below a bound; widening the bound is a coerce

(def-adts $ Addr : ((Nat) bound) -> Type
  enum
  (many MkAddr : (erased (Nat) bound) (many (Nat) n) (erased (Lt n bound) lt) -> (Addr bound)))

(def-fns _ $ many addr-path : (erased (Nat) bound) (many (Addr bound) a) -> (many (Nat) p)
  (match many a _ ((MkAddr bd n lt) n)))

(def-fns _ $ erased addr-widen : (erased (Nat) b) (erased (Nat) c) (erased (Lt b (Succ c)) le) (erased (Addr b) a) -> (erased (Addr c) a2) (erased (Coercible (Addr b) a (Addr c) a2) p)
  (match erased a _
    ((MkAddr bd n lt)
      (let (erased lt2) (lt-le-trans n b c lt le))
      (values (MkAddr c n lt2) (coercible-ctor MkAddr b c (coercible-refl n) lt lt2)))))

(def-fns _ $ many addr-weaken : (erased (Nat) b) (erased (Nat) c) (erased (Lt b (Succ c)) le) (many (Addr b) a) -> (many (Addr c) r)
  (let (erased a2) (erased p) (addr-widen b c le a))
  (coerce a p))

(def-fns _ $ erased addrs-widen : (erased (Nat) b) (erased (Nat) c) (erased (Lt b (Succ c)) le) (subterm erased (List $ Addr b) xs) -> (erased (List $ Addr c) ys) (erased (Coercible (List $ Addr b) xs (List $ Addr c) ys) p)
  (match erased xs _
    ((Nil t) (values (Nil _) (coercible-ctor Nil (Addr b) (Addr c))))
    ((Cons t x rest)
      (let (erased x2) (erased px) (addr-widen b c le x))
      (let (erased rest2) (erased pr) (addrs-widen b c le rest))
      (values (Cons _ x2 rest2) (coercible-ctor Cons (Addr b) (Addr c) px pr)))))

(def-fns _ $ many addrs-weaken : (erased (Nat) b) (erased (Nat) c) (erased (Lt b (Succ c)) le) (many (List $ Addr b) xs) -> (many (List $ Addr c) r)
  (let (erased ys) (erased p) (addrs-widen b c le xs))
  (coerce xs p))

(def-fns _ $ erased addrs-widen-lk : (erased (Nat) b) (erased (Nat) c) (erased (Lt b (Succ c)) le) (erased (List $ Nat) f) (subterm erased (List $ Addr b) xs) (erased (Lockstep (Nat) (Addr b) f xs) lk) ->
    (erased (List $ Addr c) ys) (erased (Coercible (List $ Addr b) xs (List $ Addr c) ys) p) (erased (Lockstep (Nat) (Addr c) f ys) lk2)
  (match erased xs _
    ((Nil t) (match erased lk _ ((LsNil ta tb) (values (Nil _) (coercible-ctor Nil (Addr b) (Addr c)) (LsNil _ _)))))
    ((Cons t x rest)
      (match erased lk _
        ((LsCons ta tb x0 y0 xs0 ys0 lk1)
          (let (erased x2) (erased px) (addr-widen b c le x))
          (let (erased rest2) (erased pr) (erased lk2) (addrs-widen-lk b c le xs0 rest lk1))
          (values (Cons _ x2 rest2) (coercible-ctor Cons (Addr b) (Addr c) px pr) (LsCons _ _ x0 x2 xs0 rest2 lk2)))))))

(def-fns _ $ erased maybe-widen : (erased (Nat) b) (erased (Nat) c) (erased (Lt b (Succ c)) le) (erased (Maybe $ Addr b) m) -> (erased (Maybe $ Addr c) m2) (erased (Coercible (Maybe $ Addr b) m (Maybe $ Addr c) m2) p)
  (match erased m _
    ((None t) (values (None _) (coercible-ctor None (Addr b) (Addr c))))
    ((Some t x)
      (let (erased x2) (erased px) (addr-widen b c le x))
      (values (Some _ x2) (coercible-ctor Some (Addr b) (Addr c) px)))))

(def-fns _ $ erased idmap-widen : (erased (Nat) b) (erased (Nat) c) (erased (Lt b (Succ c)) le) (subterm erased (IdMap $ Addr b) m) -> (erased (IdMap $ Addr c) m2) (erased (Coercible (IdMap $ Addr b) m (IdMap $ Addr c) m2) p)
  (match erased m _
    ((MEmpty t) (values (MEmpty _) (coercible-ctor MEmpty (Addr b) (Addr c))))
    ((MNode t here one two)
      (let (erased here2) (erased ph) (maybe-widen b c le here))
      (let (erased one2) (erased p1) (idmap-widen b c le one))
      (let (erased two2) (erased p2) (idmap-widen b c le two))
      (values (MNode _ here2 one2 two2) (coercible-ctor MNode (Addr b) (Addr c) ph p1 p2)))))

(def-fns _ $ many idmap-weaken : (erased (Nat) b) (erased (Nat) c) (erased (Lt b (Succ c)) le) (many (IdMap $ Addr b) m) -> (many (IdMap $ Addr c) r)
  (let (erased m2) (erased p) (idmap-widen b c le m))
  (coerce m p))

; ---- the heap: [B] the block type at an address, [up] the digits from a node to the root

(def-adts
  (Tree : ((TyCtor ((Nat) a) -> Type) B) ((List $ Digit) up) ((Nat) size) -> Type
    enum
    (many TLeaf : (erased (TyCtor ((Nat) a) -> Type) B) (erased (List $ Digit) up) -> (Tree B up (Zero)))
    (many TNode : (erased (TyCtor ((Nat) a) -> Type) B) (erased (List $ Digit) up) (erased (Nat) a) (erased (Wrap up (Zero) a) k)
                  (erased (Nat) l) (erased (Nat) r) (erased (Nat) s) (erased (Add l r s) sum) (erased (Braun l r) bal)
                  (many (B a) block) (many (Tree B (Cons (Digit) (D1) up) l) one) (many (Tree B (Cons (Digit) (D2) up) r) two) -> (Tree B up (Succ s))))
  (Heap : ((TyCtor ((Nat) a) -> Type) B) ((Nat) size) -> Type
    enum
    (many MkHeap : (erased (TyCtor ((Nat) a) -> Type) B) (many (Nat) size) (many (Tree B (Nil (Digit)) size) tree) -> (Heap B size))))

(def-fns _ $ many deref-at : (erased (TyCtor ((Nat) a) -> Type) B) (erased (List $ Digit) up) (erased (Nat) size) (subterm many (Tree B up size) t) (many (Nat) p) (erased (Lt p size) lt)
    (erased (Nat) key) (erased (Wrap up p key) w) -> (many (B key) b)
  (match many t _
    (absurd (TLeaf tb u) (lt-zero p lt))
    ((TNode tb u key2 k2 l r s sum bal block one two)
      (match many (nat-halve p) _
        ((HZ) (match erased (wrap-fn up (Zero) key2 key k2 w) _ ((Refl t1 x1) block)))
        ((H1 m d dd)
          (match erased lt _
            ((LtS x y lt1) (deref-at _ _ _ one m (half-lt-one m d l r s dd sum bal lt1) key (W1 _ m d dd _ w)))))
        ((H2 m d dd)
          (match erased lt _
            ((LtS x y lt1) (deref-at _ _ _ two m (half-lt-two m d l r s dd sum bal lt1) key (W2 _ m d dd _ w)))))))))

(def-fns _ $ many alloc-at : (erased (TyCtor ((Nat) a) -> Type) B) (erased (List $ Digit) up) (many (Nat) size) (subterm many (Tree B up size) t)
    (erased (Nat) key) (erased (Wrap up size key) w) (many (B key) b) -> (many (Tree B up (Succ size)) t2)
  (match many t _
    ((TLeaf tb u) (TNode _ _ key w (Zero) (Zero) (Zero) (AddZero (Zero)) (BrEq (Zero)) b (TLeaf _ _) (TLeaf _ _)))
    ((TNode tb u key2 k2 l r s sum bal block one two)
      (match many (nat-halve size) _
        ((H1 m d dd)
          (match erased bal _
            ((BrEq n)
              (match erased (double-inj m n d dd (add-diag-double n s sum)) _
                ((Refl t1 x1)
                  (TNode _ _ key2 k2 (Succ n) n (Succ s) (AddSucc n n s sum) (BrOne n) block
                    (alloc-at _ _ m one key (W1 _ m d dd _ w) b) two))))
            (absurd (BrOne n)
              (match erased sum (((False) f))
                ((AddSucc a1 b1 c1 q) (double-parity m n c1 dd (add-diag-double n c1 q)))))))
        ((H2 m d dd)
          (match erased bal _
            (absurd (BrEq n) (double-parity n m d (add-diag-double n s sum) dd))
            ((BrOne n)
              (match erased sum _
                ((AddSucc a1 b1 c1 q)
                  (match erased (double-inj m n d dd (add-diag-double n c1 q)) _
                    ((Refl t1 x1)
                      (TNode _ _ key2 k2 (Succ n) (Succ n) (Succ s) (AddSucc n (Succ n) s (add-succ-right n n c1 q)) (BrEq (Succ n)) block one
                        (alloc-at _ _ m two key (W2 _ m d dd _ w) b)))))))))))))

(def-fns _ $ many heap-empty : (erased (TyCtor ((Nat) a) -> Type) B) -> (many (Heap B (Zero)) h)
  (MkHeap _ (Zero) (TLeaf _ _)))

(def-fns _ $ many alloc : (erased (TyCtor ((Nat) a) -> Type) B) (erased (Nat) size) (many (Heap B size) h) (many (B size) b) -> (many (Heap B (Succ size)) h2) (many (Addr (Succ size)) at)
  (match many h _
    ((MkHeap tb sz tree)
      (values (MkHeap _ (Succ sz) (alloc-at _ _ sz tree sz (WNil sz) b)) (MkAddr _ sz (lt-succ sz))))))

(def-fns _ $ many deref : (erased (TyCtor ((Nat) a) -> Type) B) (erased (Nat) size) (many (Heap B size) h) (many (Addr size) at) -> (erased (Nat) a) (erased (Lt a size) lt) (many (B a) b)
  (match many h _
    ((MkHeap tb sz tree)
      (match many at _
        ((MkAddr bd n lt) (values n lt $ deref-at _ _ _ tree n lt n (WNil n)))))))

(def-fns _ $ many deref-path : (erased (TyCtor ((Nat) a) -> Type) B) (erased (Nat) size) (many (Heap B size) h) (many (Nat) p) (erased (Lt p size) lt) -> (many (B p) b)
  (match many h _
    ((MkHeap tb sz tree) (deref-at _ _ _ tree p lt p (WNil p)))))

; Every address of a heap, oldest first, counted up from zero.
(def-fns _ $ many addrs-from : (subterm many (Nat) remaining) (erased (Nat) size) (many (Nat) n) (erased (Add n remaining size) sum) -> (many (List $ Addr size) r)
  (match many remaining _
    ((Zero) (Nil _))
    ((Succ k) (Cons _ (MkAddr _ n (lt-of-add n k size sum)) $ addrs-from k _ (Succ n) (add-shift n k size sum)))))

(def-fns _ $ many heap-addrs : (erased (TyCtor ((Nat) a) -> Type) B) (erased (Nat) size) (many (Heap B size) h) -> (many (List $ Addr size) r)
  (match many h _
    ((MkHeap tb sz tree) (addrs-from sz _ (Zero) (AddZero sz)))))
