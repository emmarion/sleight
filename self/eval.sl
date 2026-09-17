; self/eval.sl -- the compile-time interpreter (KERNEL.md's round trip; lib/eval.ml): a plain recursive
; evaluator over post-erasure code and the store of self/heap.sl, bounded by a fuel that decreases along the
; call stack so the checker accepts it. Every value is an address; every step returns the grown store with
; a proof of the growth, by which what was held before is widened. Extern functions run as the host's own
; (section 41).

(def-fns _ $ erased le-refl : (erased (Hist Block) a) -> (erased (Suffix Block a a) p)
  (SfHere Block a))

(def-fns _ $ erased le-trans : (erased (Hist Block) a) (erased (Hist Block) b) (erased (Hist Block) c)
    (erased (Suffix Block b a) p) (erased (Suffix Block c b) q) -> (erased (Suffix Block c a) r)
  (suffix-trans Block c b a q p))

; What runs under: the Const entries the code names and the frames it binds.
(def-adts $ St : ((Hist Block) a) ((List $ List $ Nat) ctx) -> Type
  enum
  (many MkSt : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (IdMap $ EInfo a) consts) (many (Frames (Ref Block a) ctx) env) -> (St a ctx)))

(def-fns _ $ erased st-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le)
    (erased (List $ List $ Nat) ctx) (erased (St b ctx) st) ->
    (erased (St c ctx) r) (erased (Coercible (St b ctx) st (St c ctx) r) p)
  (match erased st _
    ((MkSt a cx cs env)
      (let (erased cs2) (erased pc) (entries-widen b c le cs))
      (let (erased env2) (erased pe) (frames-widen b c le cx env))
      (values (MkSt _ _ cs2 env2) (coercible-ctor MkSt b c cx cx pc pe)))))

(def-fns _ $ many st-consts : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (St a ctx) st) -> (many (IdMap $ EInfo a) r)
  (match many st _ ((MkSt z cx cs env) cs)))

(def-fns _ $ many st-push : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (St a ctx) st) (many (List $ Nat) f) (many (List $ Ref Block a) vs) (erased (Lockstep (Nat) (Ref Block a) f vs) lk) -> (many (St a (Cons (List (Nat)) f ctx)) r)
  (match many st _ ((MkSt z cx cs env) (MkSt _ _ cs $ FrVals _ _ f vs lk env))))

; ---- Extern values (section 41; lib/ffi_core.ml): payload blocks, read and made through the store

(def-fns _ $ many heap-nat : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) a) -> (many (Nat) n)
  (let-match many a (MkRef _ _ x rv1 rp1))
  (let-match many rv1 (MkValue _ _ pos1 lp1 b))
  (let (erased lt) (ref-suffix _ _ x rv1 rp1))
  (match many b _ ((BExt z p) (match many p _ ((PNat n) n) (else 0))) (else 0)))

(def-fns _ $ many heap-str : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) a) -> (many (String) n)
  (let-match many a (MkRef _ _ x rv2 rp2))
  (let-match many rv2 (MkValue _ _ pos2 lp2 b))
  (let (erased lt) (ref-suffix _ _ x rv2 rp2))
  (match many b _ ((BExt z p) (match many p _ ((PStr s) s) (else (SNil)))) (else (SNil))))

(def-fns _ $ many alloc-ext : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Payload) p) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a)
  (alloc Block _ hp $ BExt _ p))

(def-fns _ $ many field-nat : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (List $ Ref Block hs) fields) (many (Nat) i) -> (many (Nat) n)
  (match many (list-nth _ fields i) _ ((NthHit nt nl ni x np) (heap-nat _ hp x)) ((NthMiss nt nl ni np) 0)))

(def-fns _ $ many ext-construct : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (ExtType) ext) (many (Nat) index) (many (List $ Ref Block hs) fields) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a)
  (let (many (Payload) p)
    (match many ext _
      ((ExtNat) (PNat $ match many index (((Nat) n)) ((Zero) (Zero)) ((Succ k) (Succ $ field-nat _ hp fields 0))))
      ((ExtHalf)
        (let (many d) (erased dd) $ double $ field-nat _ hp fields 0)
        (PHalf $ match many index (((Nat) n)) ((Zero) 0) ((Succ k) (match many k (((Nat) n)) ((Zero) (Succ d)) ((Succ k2) (Succ $ Succ d))))))
      ((ExtString)
        (let (many (String) rest) $ match many (list-nth _ fields 1) _ ((NthHit nt nl ni x np) (heap-str _ hp x)) ((NthMiss nt nl ni np) (SNil)))
        (PStr $ match many index (((String) s)) ((Zero) (SNil)) ((Succ k) (SCons (char-of-code $ field-nat _ hp fields 0) rest))))))
  (alloc-ext _ hp p))

(def-fns _ $ many ext-destruct : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Payload) p) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Nat) index) (many (List $ Ref Block hs2) fields)
  (match many p _
    ((PNat n)
      (match many n _
        ((Zero) (values hs hp (le-refl hs) 0 $ Nil _))
        ((Succ k)
          (let (erased hl2) (many hp2) (erased sf2) (many a) $ alloc-ext _ hp $ PNat k)
          (values hl2 hp2 sf2 1 $ Cons _ a $ Nil _))))
    ((PHalf n)
      (match many (nat-halve n) _
        ((HZ) (values hs hp (le-refl hs) 0 $ Nil _))
        ((H1 m d dd)
          (let (erased hl2) (many hp2) (erased sf2) (many a) $ alloc-ext _ hp $ PNat m)
          (values hl2 hp2 sf2 1 $ Cons _ a $ Nil _))
        ((H2 m d dd)
          (let (erased hl2) (many hp2) (erased sf2) (many a) $ alloc-ext _ hp $ PNat m)
          (values hl2 hp2 sf2 2 $ Cons _ a $ Nil _))))
    ((PStr s)
      (match many s _
        ((SNil) (values hs hp (le-refl hs) 0 $ Nil _))
        ((SCons c rest)
          (let (erased hl2) (many hp2) (erased sf2) (many a1) $ alloc-ext _ hp $ PNat $ char-code c)
          (let (erased hl3) (many hp3) (erased sf3) (many a2) $ alloc-ext _ hp2 $ PStr rest)
          (let (erased w1) (erased p1) (ref-widen _ _ _ sf3 a1))
          (values hl3 hp3 (le-trans _ _ _ sf2 sf3) 1 $ Cons _ (coerce a1 p1) $ Cons _ a2 $ Nil _))))))

; ---- Constructing and taking apart (section 38): an untagged value is its many fields, one of them bare,
; none the token; a block's fields, bounded by its address, widen to the store's size.

(def-fns _ $ many tuple : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (List $ Ref Block hs) vs) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v)
  (match many vs _
    ((Nil a)
      (let (erased hl2) (many hp2) (erased sf2) (many v) $ alloc Block _ hp $ BToken _)
      (values hl2 hp2 sf2 v))
    ((Cons a v rest)
      (match many rest _
        ((Nil b) (values hs hp (le-refl hs) v))
        ((Cons b w rest2)
          (let (erased hl2) (many hp2) (erased sf2) (many t) $ alloc Block _ hp $ BTup _ vs)
          (values hl2 hp2 sf2 t))))))

(def-fns _ $ many untuple : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Nat) n) (many (Ref Block hs) v) -> (many (List $ Ref Block hs) vs)
  (match many n _
    ((Zero) (Nil _))
    ((Succ k)
      (match many k _
        ((Zero) (Cons _ v $ Nil _))
        ((Succ k2)
          (let-match many v (MkRef _ _ a rv3 rp3))
          (let-match many rv3 (MkValue _ _ pos3 lp3 b))
          (let (erased lt) (ref-suffix _ _ a rv3 rp3))
          (match many b _
            ((BTup z fs) (let (erased w2) (erased p2) (refs-widen _ _ _ lt fs)) (coerce fs p2)) (else (Nil $ Ref Block hs))))))))

(def-fns _ $ many construct : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ctor) c) (many (List $ Ref Block hs) args) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v)
  (match many c _
    ((MkCtor name id index arity tagged ext shape)
      (match many ext _
        ((Some a e)
          (let (erased hl2) (many hp2) (erased sf2) (many v) $ ext-construct _ hp e index args)
          (values hl2 hp2 sf2 v))
        ((None a)
          (match many tagged _
            ((BTrue)
              (let (erased hl2) (many hp2) (erased sf2) (many v) $ alloc Block _ hp $ BTag _ c args)
              (values hl2 hp2 sf2 v))
            ((BFalse) (tuple _ hp args))))))))

; A value's discriminant and many fields where the FFI holds the type or a tag says (section 38); None
; otherwise, the value then being its fields as they stand.
(def-fns _ $ many dispatch : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Maybe $ ExtType) ext) (many (Bool) tagged) (many (Ref Block hs) v) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Maybe $ Pair (Nat) $ List $ Ref Block hs2) r)
  (let-match many v (MkRef _ _ a rv4 rp4))
  (let-match many rv4 (MkValue _ _ pos4 lp4 b))
  (let (erased lt) (ref-suffix _ _ a rv4 rp4))
  (match many b _
    ((BExt z p)
      (match many ext _
        ((None e) (values hs hp (le-refl hs) $ None _))
        ((Some e t)
          (let (erased hs2) (many hp2) (erased le) (many i) (many fs) $ ext-destruct _ hp p)
          (values hs2 hp2 le $ Some _ $ MkPair _ _ i fs))))
    ((BTag z ct fs)
      (match many tagged _
        ((BTrue)
          (let (erased w3) (erased p3) (refs-widen _ _ _ lt fs))
          (values hs hp (le-refl hs) $ Some _ $ MkPair _ _ (ctor-index ct) (coerce fs p3)))
        ((BFalse) (values hs hp (le-refl hs) $ None _))))
    (else (values hs hp (le-refl hs) $ None _))))

(def-fns _ $ many destruct : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ctor) c) (many (Ref Block hs) v) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Nat) i) (many (List $ Ref Block hs2) fields)
  (match many c _
    ((MkCtor name id index arity tagged ext shape)
      (let (erased hs2) (many hp2) (erased le) (many read) $ dispatch _ hp ext tagged v)
      (match many read _
        ((Some a p) (match many p _ ((MkPair x y i fs) (values hs2 hp2 le i fs))))
        ((None a)
          (let (erased w4) (erased p4) (ref-widen _ _ _ le v))
          (values hs2 hp2 le index $ untuple _ hp2 arity (coerce v p4)))))))

(def-fns _ $ many ctor-at : (many (Adt) adt) (many (Nat) i) -> (many (Maybe $ Ctor) c)
  (match many (list-nth _ (adt-ctors adt) i) _ ((NthHit nt nl ni c np) (Some _ c)) ((NthMiss nt nl ni np) (None _))))

(def-fns _ $ many vnat : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Nat) n) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a)
  (alloc-ext _ hp $ PNat n))

; A Rope value read back for the host's flatten (ASSUMPTIONS 122); the recursion into a block's fields is
(def-fns _
  (many rope-walk : (erased (Hist Block) hs) (subterm many (Ref Block hs) r) -> (many (Rope) rope)
    (match many r _
      ((MkRef tb l0 s v p)
        (match many v _
          ((MkValue tb2 s0 pos lp body)
            (match many body _
              ((BExt z pp) (match many pp _ ((PStr str) (RStr str)) ((PNat m) (RChar $ char-of-code m)) (else (REmpty))))
              ((BTag z ct fields) (rope-fields _ fields))
              (else (REmpty))))))))
  (many rope-fields : (erased (Hist Block) hs) (subterm many (List $ Ref Block hs) fs) -> (many (Rope) rope)
    (match many fs _
      ((Nil t) (REmpty))
      ((Cons t f rest) (RCat (rope-walk _ f) (rope-fields _ rest))))))

(def-fns _ $ many flatten-value : (erased (Hist Block) hs) (many (Ref Block hs) r) -> (many (String) s)
  (let (many str) (erased p) $ flatten $ rope-walk _ r)
  str)

; An extern function over its arguments, or None where the model runs instead: nat-cmp builds a plain
; ADT (ASSUMPTIONS 120). The arguments are counted against the arity here, the call having been checked
; against the model's telescope.
(def-fns _ $ many apply-extern : (erased (Nat) n) (many (Extern n) e) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (List $ Ref Block hs) args) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Maybe $ List $ Ref Block hs2) r)
  (let (many (Maybe $ Ref Block hs) a) $ match many (list-nth _ args 0) _ ((NthHit nt nl ni x np) (Some _ x)) ((NthMiss nt nl ni np) (None _)))
  (let (many (Maybe $ Ref Block hs) b) $ match many (list-nth _ args 1) _ ((NthHit nt nl ni x np) (Some _ x)) ((NthMiss nt nl ni np) (None _)))
  (let (many (Nat) na) $ match many a _ ((Some t x) (heap-nat _ hp x)) ((None t) 0))
  (let (many (Nat) nb) $ match many b _ ((Some t x) (heap-nat _ hp x)) ((None t) 0))
  (let (many (String) sa) $ match many a _ ((Some t x) (heap-str _ hp x)) ((None t) (SNil)))
  (let (many (String) sb) $ match many b _ ((Some t x) (heap-str _ hp x)) ((None t) (SNil)))
  (let (many (Payload) p)
    (match many e _
      ((ExAdd) (PNat $ nat-add na nb))
      ((ExSub)
        (match many (lt-dec nb (Succ na)) (((Payload) q))
          ((Yes x y le) (let (many c) (erased pf) $ sub na nb le) (PNat c))
          ((No x y q) (PStr "sub: negative result"))))
      ((ExMul) (PNat $ nat-mul na nb))
      ((ExDiv)
        (match many (lt-dec (Zero) nb) (((Payload) q))
          ((Yes x y pos) (let (many d) (erased m) (erased r) (erased mm) (erased a) (erased p) $ div na nb pos) (PNat d))
          ((No x y q) (PStr "div: zero divisor"))))
      ((ExNatCmp) (PNat 0))
      ((ExNatHalve) (PHalf na))
      ((ExStrCmp) (PNat 0))
      ((ExStrSplit) (PNat 0))
      ((ExStrLength) (let (many n) (erased lp) (str-length sa)) (PNat n))
      ((ExNatStr) (PStr $ nat-str na))
      ((ExDivmod) (PNat 0))
      ((ExNatMod)
        (match many (lt-dec (Zero) nb) (((Payload) q))
          ((Yes x y pos) (let (many m) (erased pf) (erased pq) $ nat-mod na nb pos) (PNat m))
          ((No x y q) (PStr "nat-mod: zero modulus"))))
      ((ExTrim) (PStr $ trim sa))
      ((ExAppend) (PStr $ str-append sa sb))
      ((ExFlatten) (PStr $ match many a (((String) r)) ((Some t x) (flatten-value _ x)) ((None t) (SNil))))))
  (match many e _
    ((ExNatCmp) (values hs hp (le-refl hs) (None _)))
    ((ExStrCmp) (values hs hp (le-refl hs) (None _)))
    ((ExStrSplit)
      (let (many len) (erased l) $ str-length sa)
      (match many (lt-dec nb (Succ len)) _
        ((Yes x y le)
          (let (many a1) (many b1) (erased p) (erased la) $ str-split sa nb len l le)
          (let (erased hl2) (many hp2) (erased sf2) (many aa) $ alloc-ext _ hp $ PStr a1)
          (let (erased hl3) (many hp3) (erased sf3) (many ab) $ alloc-ext _ hp2 $ PStr b1)
          (let (erased wp5) (erased p5) (ref-widen _ _ _ sf3 aa))
          (values hl3 hp3 (le-trans _ _ _ sf2 sf3)
            (Some _ $ Cons _ (coerce aa p5) $ Cons _ ab $ Nil _)))
        ((No x y q)
          (let (erased hl2) (many hp2) (erased sf2) (many v) $ alloc-ext _ hp $ PStr "str-split: past the end")
          (values hl2 hp2 sf2 (Some _ $ Cons _ v $ Nil _)))))
    ((ExDivmod)
      (match many (lt-dec (Zero) nb) _
        ((Yes x y pos)
          (let (many q) (many r) (erased m) (erased mm) (erased a) (erased pr) $ divmod na nb pos)
          (let (erased hl2) (many hp2) (erased sf2) (many aq) $ alloc-ext _ hp $ PNat q)
          (let (erased hl3) (many hp3) (erased sf3) (many ar) $ alloc-ext _ hp2 $ PNat r)
          (let (erased wp6) (erased p6) (ref-widen _ _ _ sf3 aq))
          (values hl3 hp3 (le-trans _ _ _ sf2 sf3)
            (Some _ $ Cons _ (coerce aq p6) $ Cons _ ar $ Nil _)))
        ((No x y q)
          (let (erased hl2) (many hp2) (erased sf2) (many v) $ alloc-ext _ hp $ PStr "divmod: zero divisor")
          (values hl2 hp2 sf2 (Some _ $ Cons _ v $ Nil _)))))
    (else
      (let (erased hl2) (many hp2) (erased sf2) (many v) $ alloc-ext _ hp p)
      (values hl2 hp2 sf2 (Some _ $ Cons _ v $ Nil _)))))

; ---- Values at every position of a code's index (ASSUMPTIONS 125)

(def-fns _ $ many vals-of : (erased (Hist Block) hs) (subterm many (List $ Mult) ms) (many (Ref Block hs) v) -> (many (Vals hs ms) r)
  (match many ms _
    ((Nil a) (ValsNil _))
    ((Cons a m rest) (match many m _ ((Many) (ValsMany _ _ v $ vals-of _ rest v)) ((Erased) (ValsErased _ _ $ vals-of _ rest v))))))

(def-fns _ $ many error-vals : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (List $ Mult) ms) (many (String) msg) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Vals hs2 ms) vs)
  (let (erased hl2) (many hp2) (erased sf2) (many e) $ alloc Block _ hp $ BError _ msg)
  (values hl2 hp2 sf2 $ vals-of _ ms e))

; Cut or padded to the index, a closure's arity being a runtime property; a missing value is an error block.
(def-fns _ $ many vals-fit : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Mult) ms) (many (List $ Ref Block hs) vs) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Vals hs2 ms) r)
  (match many ms _
    ((Nil a) (values hs hp (le-refl hs) $ ValsNil _))
    ((Cons a m rest)
      (match many m _
        ((Erased)
          (let (erased hs2) (many hp2) (erased le) (many r) $ vals-fit _ hp rest vs)
          (values hs2 hp2 le $ ValsErased _ _ r))
        ((Many)
          (match many vs _
            ((Nil b)
              (let (erased hl2) (many hp2) (erased sf2) (many e) $ alloc Block _ hp $ BError _ "arity mismatch")
              (let (erased hs3) (many hp3) (erased le3) (many r) $ vals-fit _ hp2 rest $ Nil _)
              (let (erased we1) (erased pe1) (ref-widen _ _ _ le3 e))
              (values hs3 hp3 (le-trans _ _ _ sf2 le3) $ ValsMany _ _ (coerce e pe1) r))
            ((Cons b v vrest)
              (let (erased hs2) (many hp2) (erased le) (many r) $ vals-fit _ hp rest vrest)
              (let (erased wv1) (erased pv1) (ref-widen _ _ _ le v))
              (values hs2 hp2 le $ ValsMany _ _ (coerce v pv1) r))))))))

(def-fns _ $ many vals-list : (erased (Hist Block) hs) (erased (List $ Mult) ms) (subterm many (Vals hs ms) vs) -> (many (List $ Ref Block hs) r)
  (match many vs _
    ((ValsNil a) (Nil _))
    ((ValsMany a m v rest) (Cons _ v $ vals-list _ _ rest))
    ((ValsErased a m rest) (vals-list _ _ rest))))

(def-fns _ $ many vals-one : (erased (Hist Block) hs) (many (Vals hs many-one) vs) -> (many (Ref Block hs) v)
  (match many vs _ ((ValsMany a m v rest) v)))

; The many values of [vs] as the frame of the ids picked from the same positions.
(def-fns _ $ many vals-frame : (erased (Hist Block) hs) (erased (List $ Mult) ms) (erased (List $ Nat) ids) (erased (Picked (Nat) ms ids) pk) (subterm many (Vals hs ms) vs) -> (many (List $ Ref Block hs) r) (erased (Lockstep (Nat) (Ref Block hs) ids r) lk)
  (match many vs _
    ((ValsNil a) (match erased pk _ ((PkNil t) (values (Nil _) (LsNil _ _)))))
    ((ValsMany a m v rest)
      (match erased pk _
        ((PkMany ta ms2 x xs p)
          (let (many r) (erased lk) $ vals-frame _ _ _ p rest)
          (values (Cons _ v r) (LsCons _ _ x v xs r lk)))))
    ((ValsErased a m rest)
      (match erased pk _
        ((PkErased ta ms2 xs p) (vals-frame _ _ _ p rest))))))

; A branch's fields or a closure's arguments bound to their ids, cut or padded to their count.
(def-fns _ $ many fit-addrs : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Nat) ids) (many (List $ Ref Block hs) vs) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r) (erased (Lockstep (Nat) (Ref Block hs2) ids r) lk)
  (match many ids _
    ((Nil a) (values hs hp (le-refl hs) (Nil _) (LsNil _ _)))
    ((Cons a x rest)
      (match many vs _
        ((Nil b)
          (let (erased hl2) (many hp2) (erased sf2) (many e) $ alloc Block _ hp $ BError _ "arity mismatch")
          (let (erased hs3) (many hp3) (erased le3) (many r) (erased lk) $ fit-addrs _ hp2 rest $ Nil _)
          (let (erased we2) (erased pe2) (ref-widen _ _ _ le3 e))
          (let (many e2) (coerce e pe2))
          (values hs3 hp3 (le-trans _ _ _ sf2 le3) (Cons _ e2 r) (LsCons _ _ x e2 rest r lk)))
        ((Cons b v vrest)
          (let (erased hs2) (many hp2) (erased le) (many r) (erased lk) $ fit-addrs _ hp rest vrest)
          (let (erased wv2) (erased pv2) (ref-widen _ _ _ le v))
          (let (many v2) (coerce v pv2))
          (values hs2 hp2 le (Cons _ v2 r) (LsCons _ _ x v2 rest r lk)))))))

(def-fns _ $ many at-index : (erased (Nat) x) (erased (List $ Nat) f) (subterm many (At x f) p) -> (many (Nat) i)
  (match many p _ ((AtHere y rest) 0) ((AtThere y z rest q) (Succ $ at-index _ _ q))))

; A variable's value: from a frame of values by its place, or, in a group's frame, the member's closure
; made over the group's block.
(def-fns _ $ many frames-get : (erased (Nat) x) (erased (List $ List $ Nat) ctx) (subterm many (Mem x ctx) p) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Frames (Ref Block hs) ctx) env) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v)
  (match many p _
    ((MHere y f c q)
      (match many env _
        ((FrVals a c2 f2 vs lk rest)
          (let (many v) (erased sq) $ at-get _ _ _ q vs lk)
          (values hs hp (le-refl hs) v))
        ((FrGroup a c2 gids g rest)
          (let (many i) $ at-index _ _ q)
          (let (erased hl2) (many hp2) (erased sf2) (many v) $ alloc Block _ hp $ BFn _ g i $ list-nth-or _ gids i (Zero))
          (values hl2 hp2 sf2 v))))
    ((MThere y f c q)
      (match many env _
        ((FrVals a c2 f2 vs lk rest) (frames-get _ _ q _ hp rest))
        ((FrGroup a c2 gids g rest) (frames-get _ _ q _ hp rest))))))

(def-fns _ $ many has-branch : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) i) -> (many (Bool) r)
  (match many bs _
    ((Nil a) (BFalse))
    ((Cons a b rest) (match many b _ ((MkBranch c n0 d ids body) (or (nat-eq d i) $ has-branch _ _ rest i))))))

(def-fns _ $ many error-list : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (String) msg) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs)
  (let (erased hl2) (many hp2) (erased sf2) (many e) $ alloc Block _ hp $ BError _ msg)
  (values hl2 hp2 sf2 $ Cons _ e $ Nil _))

(def-fns _
  (many eval : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (St hs ctx) st) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Vals hs2 ms) vs)
    (match many code _
      ((CVar c x p)
        (match many st _
          ((MkSt a cx cs env)
            (let (erased h2) (many hp2) (erased le) (many v) $ frames-get _ _ p _ hp env)
            (values h2 hp2 le $ ValsMany _ _ v $ ValsNil _))))
      ((CConst c x)
        (match many (idmap-get _ x $ st-consts _ _ st) _
          ((Hit ht hk hm info hq)
            (match many info _
              ((MkEInfo z n m s mi me)
                (match many s _
                  ((SConst z2 v) (values hs hp (le-refl hs) $ ValsMany _ _ v $ ValsNil _))
                  ((SDyn z2) (error-vals _ hp many-one "a Dyn constant"))))))
          ((Miss ht hk hm hq) (error-vals _ hp many-one "unbound constant"))))
      ((CValue c v)
        (let (erased wv3) (erased pv3) (block-widen _ _ (empty-suffix _ hs) v))
        (let (erased hl2) (many hp2) (erased sf2) (many a) $ alloc Block _ hp (coerce v pv3))
        (values hl2 hp2 sf2 $ ValsMany _ _ a $ ValsNil _))
      ((CErased c ms2)
        (let (erased hl2) (many hp2) (erased sf2) (many a) $ alloc Block _ hp $ BToken _)
        (values hl2 hp2 sf2 $ vals-of _ ms2 a))
      ((CValues c ms2 cs2 pk) (eval-picked fuel _ hp _ cs2 ms2 pk st))
      ((CApp c ms2 f args cc)
        (let (erased h1) (many hp1) (erased le1) (many fvs) $ eval fuel _ hp _ _ f st)
        (let (erased ws1) (erased ps1) (st-widen _ _ le1 _ st))
        (let (erased h2) (many hp2) (erased le2) (many avs) $ eval-list fuel _ hp1 _ args (coerce st ps1))
        (let (many fv0) $ vals-one _ fvs)
        (let (erased wf0) (erased pf0) (ref-widen _ _ _ le2 fv0))
        (let (many fv) (coerce fv0 pf0))
        (match many fuel _
          ((Zero)
            (let (erased h3) (many hp3) (erased le3) (many r) $ error-vals _ hp2 ms2 "out of fuel")
            (values h3 hp3 (le-trans _ _ _ (le-trans _ _ _ le1 le2) le3) r))
          ((Succ k)
            (let (many cs0) $ st-consts _ _ st)
            (let (erased wc0) (erased pc0) (entries-widen _ _ (le-trans _ _ _ le1 le2) cs0))
            (let (erased h3) (many hp3) (erased le3) (many rs) $ apply k _ hp2 (coerce cs0 pc0) fv avs)
            (let (erased h4) (many hp4) (erased le4) (many r) $ vals-fit _ hp3 ms2 rs)
            (values h4 hp4 (le-trans _ _ _ (le-trans _ _ _ le1 le2) (le-trans _ _ _ le3 le4)) r))))
      ((CLet c ms2 ns ids pk rhs rest)
        (let (erased h1) (many hp1) (erased le1) (many rvs) $ eval fuel _ hp _ _ rhs st)
        (let (many vs) (erased lk) $ vals-frame _ _ _ pk rvs)
        (let (erased ws2) (erased ps2) (st-widen _ _ le1 _ st))
        (let (erased h2) (many hp2) (erased le2) (many r) $ eval fuel _ hp1 _ _ rest $ st-push _ _ (coerce st ps2) ids vs lk)
        (values h2 hp2 (le-trans _ _ _ le1 le2) r))
      ((CLetRec c ns gids g rest)
        (match many st _
          ((MkSt a cx cs env)
            (match many g _
              ((MkGroup c1 ids fns lk)
                (let (erased hl1) (many hp1) (erased sf1) (many ga) $ alloc Block _ hp $ BGroup _ _ _ g env)
                (let (erased le1) sf1)
                (let (erased wc1) (erased pc1) (entries-widen _ _ le1 cs))
                (let (erased wn1) (erased pn1) (frames-widen _ _ le1 _ env))
                (let (erased h2) (many hp2) (erased le2) (many r) $ eval fuel _ hp1 _ _ rest $ MkSt _ _ (coerce cs pc1) (FrGroup _ _ ids ga (coerce env pn1)))
                (values h2 hp2 (le-trans _ _ _ le1 le2) r))))))
      ((CMatch c ns scrut shape branches dfl live)
        (let (erased h1) (many hp1) (erased le1) (many svs) $ eval fuel _ hp _ _ scrut st)
        (let (many v) $ vals-one _ svs)
        (let (erased ws3) (erased ps3) (st-widen _ _ le1 _ st))
        (let (many st1) (coerce st ps3))
        (let (erased (Hist Block) h2) (many (Store Block h2) hp2) (erased (Suffix Block h2 h1) le2) (many (Maybe $ Pair (Nat) $ List $ Ref Block h2) read)
          (match many shape _
            ((ShKnown c2 adt) (dispatch _ hp1 (adt-ext adt) (adt-tagged adt) v))
            ((ShNone c2) (values h1 hp1 (le-refl h1) $ None _))
            ((ShHeld c2 mcode held)
              (let (erased h1b) (many hp1b) (erased le1b) (many mvs) $ eval fuel _ hp1 _ _ mcode st1)
              (let (many mref) $ vals-one _ mvs)
              (let-match many mref (MkRef _ _ ma rv5 rp5))
              (let-match many rv5 (MkValue _ _ pos5 lp5 mb))
              (let (erased mlt) (ref-suffix _ _ ma rv5 rp5))
              (match many mb (((Hist Block) h) ((Store Block h) p) ((Suffix Block h h1) l) ((Maybe $ Pair (Nat) $ List $ Ref Block h) r))
                ((BMat z a)
                  (let (erased wv4) (erased pv4) (ref-widen _ _ _ le1b v))
                  (let (erased h1c) (many hp1c) (erased le1c) (many r) $ dispatch _ hp1b (adt-ext a) (adt-tagged held) (coerce v pv4))
                  (values h1c hp1c (le-trans _ _ _ le1b le1c) r))
                (else (values h1b hp1b le1b $ None _))))))
        (let (erased ws4) (erased ps4) (st-widen _ _ le2 _ st1))
        (let (many st2) (coerce st1 ps4))
        (let (erased wv5) (erased pv5) (ref-widen _ _ _ le2 v))
        (let (many v2) (coerce v pv5))
        (let (erased (Hist Block) h3) (many (Store Block h3) hp3) (erased (Suffix Block h3 h2) le3) (many (Vals h3 ns) r)
          (match many read _
            ((Some a p)
              (match many p _
                ((MkPair x y i fields)
                  (match many (has-branch _ _ branches i) _
                    ((BTrue) (eval-branch fuel _ hp2 _ ns branches i fields st2))
                    ((BFalse) (match many dfl _ ((Some b d) (eval fuel _ hp2 _ _ d $ st-push _ _ st2 (Nil _) (Nil _) (LsNil _ _))) ((None b) (eval-branch fuel _ hp2 _ ns branches i fields st2))))))))
            ((None a)
              (match many branches _
                ((Nil b) (match many dfl _ ((Some c2 d) (eval fuel _ hp2 _ _ d $ st-push _ _ st2 (Nil _) (Nil _) (LsNil _ _))) ((None c2) (error-vals _ hp2 ns "no branch"))))
                ((Cons b br rest)
                  (match many br _
                    ((MkBranch c2 n0 d ids body)
                      (let (erased h2b) (many hp2b) (erased le2b) (many fs) (erased lk) $ fit-addrs _ hp2 ids $ untuple _ hp2 (list-length _ ids) v2)
                      (let (erased ws5) (erased ps5) (st-widen _ _ le2b _ st2))
                      (let (erased h2c) (many hp2c) (erased le2c) (many r) $ eval fuel _ hp2b _ _ body $ st-push _ _ (coerce st2 ps5) ids fs lk)
                      (values h2c hp2c (le-trans _ _ _ le2b le2c) r))))))))
        (values h3 hp3 (le-trans _ _ _ (le-trans _ _ _ le1 le2) le3) r))
      ((CAbsurd c ms2) (error-vals _ hp ms2 "absurd code reached"))
      ((CError c ms2 m) (error-vals _ hp ms2 m))))

  (many eval-list : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (St hs ctx) st) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs)
    (match many cs _
      ((Nil a) (values hs hp (le-refl hs) $ Nil _))
      ((Cons a c rest)
        (let (erased h1) (many hp1) (erased le1) (many vs1) $ eval fuel _ hp _ _ c st)
        (let (erased ws6) (erased ps6) (st-widen _ _ le1 _ st))
        (let (erased h2) (many hp2) (erased le2) (many vs) $ eval-list fuel _ hp1 _ rest (coerce st ps6))
        (let (many vo1) $ vals-one _ vs1)
        (let (erased wo1) (erased po1) (ref-widen _ _ _ le2 vo1))
        (values h2 hp2 (le-trans _ _ _ le1 le2) $ Cons _ (coerce vo1 po1) vs))))

  (many eval-picked : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (subterm many (List $ Mult) ms) (erased (Picked (Code ctx many-one) ms cs) pk) (many (St hs ctx) st) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Vals hs2 ms) vs)
    (match many ms _
      ((Nil a) (values hs hp (le-refl hs) $ ValsNil _))
      ((Cons a m rest)
        (match many m _
          ((Many)
            (match erased pk _
              ((PkMany ta ms2 c0 cs2 p)
                (match many cs _
                  ((Cons b c crest)
                    (let (erased h1) (many hp1) (erased le1) (many vs1) $ eval fuel _ hp _ _ c st)
                    (let (erased ws7) (erased ps7) (st-widen _ _ le1 _ st))
                    (let (erased h2) (many hp2) (erased le2) (many vs) $ eval-picked fuel _ hp1 _ crest rest p (coerce st ps7))
                    (let (many vo2) $ vals-one _ vs1)
                    (let (erased wo2) (erased po2) (ref-widen _ _ _ le2 vo2))
                    (values h2 hp2 (le-trans _ _ _ le1 le2) $ ValsMany _ _ (coerce vo2 po2) vs))))))
          ((Erased)
            (match erased pk _
              ((PkErased ta ms2 cs2 p)
                (let (erased h2) (many hp2) (erased le2) (many vs) $ eval-picked fuel _ hp _ cs rest p st)
                (values h2 hp2 le2 $ ValsErased _ _ vs))))))))

  (many eval-branch : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (erased (List $ List $ Nat) ctx) (many (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) i) (many (List $ Ref Block hs) fields) (many (St hs ctx) st) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Vals hs2 ns) vs)
    (match many bs _
      ((Nil a) (error-vals _ hp ns $ str-cat "no branch for discriminant " $ nat-str i))
      ((Cons a b rest)
        (match many b _
          ((MkBranch c n0 d ids body)
            (match many (nat-cmp d i) _
              ((CEq eq-t eq-r eq-x)
                (let (erased h1) (many hp1) (erased le1) (many fs) (erased lk) $ fit-addrs _ hp ids fields)
                (let (erased ws8) (erased ps8) (st-widen _ _ le1 _ st))
                (let (erased h2) (many hp2) (erased le2) (many r) $ eval fuel _ hp1 _ _ body $ st-push _ _ (coerce st ps8) ids fs lk)
                (values h2 hp2 (le-trans _ _ _ le1 le2) r))
              (else (eval-branch fuel _ hp _ ns rest i fields st))))))))

  ; A closure is a member of the group at its block: the body runs over the parameters, the group's frame
  ; and the frames the group closed over. A missing member is an error block (ASSUMPTIONS 127).
  (many apply : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) cs) (many (Ref Block hs) f) (many (List $ Ref Block hs) args) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs)
    (let-match many f (MkRef _ _ fa rv6 rp6))
    (let-match many rv6 (MkValue _ _ pos6 lp6 fb))
    (let (erased flt) (ref-suffix _ _ fa rv6 rp6))
    (match many fb _
      ((BFn z ga i id)
        (let (erased wg1) (erased pg1) (ref-widen _ _ _ flt ga))
        (let (many g) (coerce ga pg1))
        (let-match many g (MkRef _ _ gn rv7 rp7))
        (let-match many rv7 (MkValue _ _ pos7 lp7 gb))
        (let (erased glt) (ref-suffix _ _ gn rv7 rp7))
        (match many gb _
          ((BGroup z2 gids ctx group cenv)
            (match many group _
              ((MkGroup c ids fns lk)
                (match many (list-nth _ fns i) _
                  ((NthMiss nt nl ni np) (error-list _ hp "no such member"))
                  ((NthHit nt nl ni p np)
                    (match many p _
                      ((MkPair x y id fn)
                        (match many fn _
                          ((MkFunc gg cc rets name fid params body impl top)
                            (let (erased (Hist Block) h1) (many (Store Block h1) hp1) (erased (Suffix Block h1 hs) le1) (many (Maybe $ List $ Ref Block h1) done)
                              (match many impl _
                                ((None a) (values hs hp (le-refl hs) $ None _))
                                ((Some a se)
                                  (match many se _
                                    ((MkSomeExtern n e) (apply-extern _ e _ hp args))))))
                            (match many done _
                              ((Some a r) (values h1 hp1 le1 r))
                              ((None a)
                                (match many fuel _
                                  ((Zero)
                                    (let (erased h3) (many hp3) (erased le3) (many r) $ error-list _ hp1 "out of fuel")
                                    (values h3 hp3 (le-trans _ _ _ le1 le3) r))
                                  ((Succ k)
                                    (let (erased wa1) (erased pa1) (refs-widen _ _ _ le1 args))
                                    (let (erased h2) (many hp2) (erased le2) (many vs) (erased lkp) $ fit-addrs _ hp1 params (coerce args pa1))
                                    (let (erased le12) (le-trans _ _ _ le1 le2))
                                    (let (erased wg2) (erased pg2) (ref-widen _ _ _ le12 g))
                                    (let (erased wn2) (erased pn2) (frames-widen _ _ (le-trans _ _ _ glt le12) _ cenv))
                                    (let (many env) $ FrVals _ _ params vs lkp $ FrGroup _ _ ids (coerce g pg2) (coerce cenv pn2))
                                    (let (erased wc2) (erased pc2) (entries-widen _ _ le12 cs))
                                    (let (erased h3) (many hp3) (erased le3) (many r) $ eval k _ hp2 _ _ body $ MkSt _ _ (coerce cs pc2) env)
                                    (values h3 hp3 (le-trans _ _ _ le12 le3) $ vals-list _ _ r))))))))))))))
          (else (error-list _ hp "not a group"))))
      ((BCtorFn z c)
        (let (erased h2) (many hp2) (erased le2) (many v) $ construct _ hp c args)
        (values h2 hp2 le2 $ Cons _ v $ Nil _))
      ((BError z m) (error-list _ hp m))
      (else (error-list _ hp "cannot apply a value that is not a function")))))

(let (many eval-fuel) 1000000)

(def-fns _ $ many run-code : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) cs) (erased (List $ Mult) ms) (many (Code (Nil (List (Nat))) ms) code) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Vals hs2 ms) vs)
  (eval eval-fuel _ hp _ _ code $ MkSt _ _ cs $ FrNil _))

; ---- Run-position statements against the environment (section 34): each reads the store out, runs or
; allocates, and puts it back with what holds its addresses widened.

(def-fns _ $ many set-states : (erased (Hist Block) hs) (many (IdMap $ EInfo hs) en) (subterm many (List $ Nat) ids) (many (List $ Ref Block hs) vs) (erased (Lockstep (Nat) (Ref Block hs) ids vs) lk) -> (many (IdMap $ EInfo hs) r)
  (match many ids _
    ((Nil a) en)
    ((Cons a x rest)
      (match erased lk _
        ((LsCons ta tb x0 v0 xs vrest0 p)
          (match many vs _
            ((Cons b v vrest) (set-states _ (entries-set-state _ en x $ SConst _ v) rest vrest p))))))))

(def-fns _ $ many env-run-final : (many (Env) e) (many (Code (Nil (List (Nat))) many-one) code) (many (Term) ty) -> (many (Env) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (let (erased hs2) (many hp2) (erased le) (many vs) $ run-code _ hp en _ code)
  (let (many en2) (many fi2) $ store-grow _ _ le en fi)
  (env-with-store e _ hp2 en2 $ Cons _ (MkPair _ _ (vals-one _ vs) ty) fi2))

(def-fns _ $ many close-members : (many (Env) e) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) en) (many (List $ Pair (Ref Block hs) $ Term) fi) (subterm many (List $ Nat) ids) (many (Ref Block hs) g) (many (Nat) i) -> (many (Env) r)
  (match many ids _
    ((Nil a) (env-with-store e _ hp en fi))
    ((Cons a x rest)
      (let (erased hl2) (many hp2) (erased sf2) (many v) $ alloc Block _ hp $ BFn _ g i x)
      (let (erased le) sf2)
      (let (many en2) (many fi2) $ store-grow _ _ le en fi)
      (let (erased wg3) (erased pg3) (ref-widen _ _ _ le g))
      (close-members e _ hp2 (entries-set-state _ en2 x $ SConst _ v) fi2 rest (coerce g pg3) $ Succ i))))

; A run-position def-fns: the group's block over no frames, then a closure block per member.
(def-fns _ $ many env-close-group : (many (Env) e) (erased (List $ Nat) gids) (many (Group gids (Nil (List (Nat)))) g) -> (many (Env) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (let (erased hl1) (many hp1) (erased sf1) (many ga) $ alloc Block _ hp $ BGroup _ _ _ g $ FrNil _)
  (let (many en1) (many fi1) $ store-grow _ _ sf1 en fi)
  (match many g _ ((MkGroup c ids fns lk) (close-members e _ hp1 en1 fi1 ids ga 0))))

; The Const fields of a value bound to their ids at their declared multiplicities (section 15): a many
; field its address, an erased one the token, a missing one an error block.
(def-fns _ $ many set-field-states : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) en) (many (List $ Pair (Ref Block hs) $ Term) fi) (subterm many (List $ Nat) fids) (many (List $ Mult) mults) (many (List $ Ref Block hs) vs) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (many (IdMap $ EInfo hs2) en2) (many (List $ Pair (Ref Block hs2) $ Term) fi2)
  (match many fids _
    ((Nil a) (values hs hp en fi))
    ((Cons a x rest)
      (let (many (Mult) m) (many (List $ Mult) mrest) $ match many mults _ ((Nil b) (values (Many) $ Nil _)) ((Cons b m0 mr) (values m0 mr)))
      (let (many (Block (Ref Block hs)) filler) $ match many m _ ((Many) (BError _ "missing value")) ((Erased) (BToken _)))
      (let (many (Maybe $ Ref Block hs) have) $ match many m _ ((Erased) (None _)) ((Many) (match many vs (((Maybe $ Ref Block hs) r)) ((Nil b) (None _)) ((Cons b v vrest) (Some _ v)))))
      (let (many (List $ Ref Block hs) vrest) $ match many m _ ((Erased) vs) ((Many) (match many vs (((List $ Ref Block hs) r)) ((Nil b) (Nil _)) ((Cons b v vr) vr))))
      (match many have _
        ((Some b v) (set-field-states _ hp (entries-set-state _ en x $ SConst _ v) fi rest mrest vrest))
        ((None b)
          (let (erased hl2) (many hp2) (erased sf2) (many t) $ alloc Block _ hp filler)
          (let (erased le) sf2)
          (let (many en2) (many fi2) $ store-grow _ _ le en fi)
          (let (erased wr1) (erased pr1) (refs-widen _ _ _ le vrest))
          (set-field-states _ hp2 (entries-set-state _ en2 x $ SConst _ t) fi2 rest mrest (coerce vrest pr1)))))))

(def-fns _ $ many env-run-let : (many (Env) e) (many (List $ Mult) ms) (many (Code (Nil (List (Nat))) ms) code) (many (List $ Nat) ids) -> (many (Env) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (let (erased hs2) (many hp2) (erased le) (many vs) $ run-code _ hp en _ code)
  (let (many en2) (many fi2) $ store-grow _ _ le en fi)
  (let (erased hs3) (many hp3) (many en3) (many fi3) $ set-field-states _ hp2 en2 fi2 ids ms $ vals-list _ _ vs)
  (env-with-store e _ hp3 en3 fi3))

; The discriminant of a Const entry's value under a constructor's reading, or None where it is no Const.
(def-fns _ $ many env-destruct : (many (Env) e) (many (Nat) x) (many (Ctor) ct) -> (many (Env) r) (many (Maybe $ Nat) i)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (match many (idmap-get _ x en) _
    ((Miss ht hk hm hq) (values e $ None _))
    ((Hit ht hk hm info hq)
      (match many info _
        ((MkEInfo z n m s mi me)
          (match many s _
            ((SDyn z2) (values e $ None _))
            ((SConst z2 v)
              (let (erased hs2) (many hp2) (erased le) (many i) (many fs) $ destruct _ hp ct v)
              (let (many en2) (many fi2) $ store-grow _ _ le en fi)
              (values (env-with-store e _ hp2 en2 fi2) $ Some _ i))))))))

(def-fns _ $ many env-set-fields : (many (Env) e) (many (Nat) x) (many (Ctor) ct) (many (List $ Nat) fids) (many (List $ Mult) mults) -> (many (Env) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (match many (idmap-get _ x en) _
    ((Miss ht hk hm hq) e)
    ((Hit ht hk hm info hq)
      (match many info _
        ((MkEInfo z n m s mi me)
          (match many s _
            ((SDyn z2) e)
            ((SConst z2 v)
              (let (erased hs2) (many hp2) (erased le) (many i) (many fs) $ destruct _ hp ct v)
              (let (many en2) (many fi2) $ store-grow _ _ le en fi)
              (let (erased hs3) (many hp3) (many en3) (many fi3) $ set-field-states _ hp2 en2 fi2 fids mults fs)
              (env-with-store e _ hp3 en3 fi3))))))))

; A run-position let-match: the scrutinee's code run and its fields bound (section 16).
(def-fns _ $ many env-run-fields : (many (Env) e) (many (Code (Nil (List (Nat))) many-one) code) (many (Ctor) ct) (many (List $ Nat) fids) (many (List $ Mult) mults) -> (many (Env) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (let (erased hs1) (many hp1) (erased le1) (many vs) $ run-code _ hp en _ code)
  (let (erased hs2) (many hp2) (erased le2) (many i) (many fs) $ destruct _ hp1 ct $ vals-one _ vs)
  (let (many en2) (many fi2) $ store-grow _ _ (le-trans _ _ _ le1 le2) en fi)
  (let (erased hs3) (many hp3) (many en3) (many fi3) $ set-field-states _ hp2 en2 fi2 fids mults fs)
  (env-with-store e _ hp3 en3 fi3))

; Every binder of a run-position statement that did not run holds the token, as after an error.
(def-fns _ $ many env-set-tokens : (many (Env) e) (subterm many (List $ Nat) ids) -> (many (Env) r)
  (match many ids _
    ((Nil a) e)
    ((Cons a x rest) (env-set-tokens (set-state-closed e x $ BToken _) rest))))
