; self/eval.sl -- the compile-time interpreter (KERNEL.md's round trip; lib/eval.ml): a plain recursive
; evaluator over post-erasure code and the store of self/heap.sl, bounded by a fuel that decreases along the
; call stack so the checker accepts it. Every value is an address; every step returns the grown store with
; a proof of the growth, by which what was held before is widened. Extern functions run as the host's own
; (section 41).

(def-fns _ $ (erased le-refl : (erased (Hist Block) a) -> (erased (Suffix Block a a) p))
  (SfHere Block a))

(def-fns _ $ (erased le-trans : (erased (Hist Block) a) (erased (Hist Block) b) (erased (Hist Block) c)
    (erased (Suffix Block b a) p) (erased (Suffix Block c b) q) -> (erased (Suffix Block c a) r))
  (suffix-trans Block c b a q p))

; What runs under: the Const entries the code names and the frames it binds.
(def-adts $ (St : ((Hist Block) a) ((List $ List $ Nat) ctx) -> Type)
  enum
  (many MkSt : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (IdMap $ EInfo a) consts) (many (Frames (Ref Block a) ctx) env) -> (St a ctx)))

(def-fns _ $ (erased st-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le)
    (erased (List $ List $ Nat) ctx) (erased (St b ctx) st) ->
    (erased (St c ctx) r) (erased (Coercible (Shared) (St b ctx) st (Shared) (St c ctx) r) p))
  (match erased st _
    ((MkSt a cx cs env)
      (let ((erased cs2) (erased pc)) (entries-widen b c le cs))
      (let ((erased env2) (erased pe)) (frames-widen b c le cx env))
      (values (MkSt _ _ cs2 env2) (coercible-ctor (Shared) MkSt b c cx cx pc pe)))))

(def-fns _ $ (many st-consts : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (St a ctx) st) -> (many (IdMap $ EInfo a) r))
  (match many st _ ((MkSt z cx cs env) cs)))

(def-fns _ $ (many st-push : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (St a ctx) st) (many (List $ Nat) f) (many (List $ Ref Block a) vs) (erased (Lockstep (Nat) (Ref Block a) f vs) lk) -> (many (St a (Cons (List (Nat)) f ctx)) r))
  (match many st _ ((MkSt z cx cs env) (MkSt _ _ cs $ FrVals _ _ f vs lk env))))

; ---- Extern values (section 41; lib/ffi_core.ml): payload blocks, read and made through the store

(def-fns _ $ (many heap-nat : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) a) -> (many (Nat) n))
  (let ((erased x) (many b) (erased lt)) (store-read Block _ hp a))
  (match many b _ ((BExt z p) (match many p _ ((PNat n) n) (else 0))) (else 0)))

(def-fns _ $ (many heap-str : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) a) -> (many (String) n))
  (let ((erased x) (many b) (erased lt)) (store-read Block _ hp a))
  (match many b _ ((BExt z p) (match many p _ ((PStr s) s) (else (SNil)))) (else (SNil))))

(def-fns _ $ (many alloc-ext : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Payload) p) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a))
  (alloc Block _ hp $ BExt _ p))

(def-fns _ $ (many field-nat : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (List $ Ref Block hs) fields) (many (Nat) i) -> (many (Nat) n))
  (match many (list-nth _ fields i) _ ((NthHit nt nl ni x np) (heap-nat _ hp x)) ((NthMiss nt nl ni np) 0)))

(def-fns _ $ (many replace-field : (erased Type A) (subterm many (List A) fields)
    (many (Nat) index) (many A value) -> (many (List A) out))
  (match many fields _
    ((Nil t) (Nil _))
    ((Cons t x rest)
      (match many index _
        ((Zero) (Cons _ value rest))
        ((Succ k) (Cons _ x (replace-field _ rest k value)))))))

(def-fns _ $ (many replace-fields : (erased Type A) (many (List A) fields)
    (subterm many (List $ Nat) indices) (many (List A) values) -> (many (List A) out))
  (match many indices _
    ((Nil t) fields)
    ((Cons t i rest)
      (match many values _
        ((Nil a) fields)
        ((Cons a v tail) (replace-fields _ (replace-field _ fields i v) rest tail))))))

(def-adts $ (ArrayView : (Type R) -> Type) enum
  (many MkArrayView : (erased Type R) (many R backing) (many (Nat) offset) (many (Nat) length) -> (ArrayView R)))

(def-fns _ $ (many array-view : (erased (Hist Block) hs) (many (Store Block hs) hp)
    (many (Ref Block hs) v) -> (many (Maybe $ ArrayView $ Ref Block hs) view))
  (let ((erased s) (many body) (erased sf)) (store-read Block _ hp v))
  (match many body _
    ((BArray z backing offset length)
      (let ((erased b2) (erased pb)) (ref-widen _ _ _ sf backing))
      (Some _ (MkArrayView _ (coerce backing pb) offset length)))
    (else (None _))))

(def-fns _ $ (many backing-fields : (erased (Hist Block) hs) (many (Store Block hs) hp)
    (many (Ref Block hs) backing) -> (many (List $ Ref Block hs) fields))
  (let ((erased s) (many body) (erased sf)) (store-read Block _ hp backing))
  (match many body _
    ((BArrayData z fields)
      (let ((erased fs2) (erased pf)) (refs-widen _ _ _ sf fields))
      (coerce fields pf))
    (else (Nil _))))

(def-fns _ $ (many take-fields : (erased Type A) (subterm many (List A) fields)
    (many (Nat) count) -> (many (List A) out))
  (match many fields _
    ((Nil t) (Nil _))
    ((Cons t x rest)
      (match many count _ ((Zero) (Nil _)) ((Succ k) (Cons _ x (take-fields _ rest k)))))))

(def-fns _ $ (many slice-fields : (erased Type A) (subterm many (List A) fields)
    (many (Nat) offset) (many (Nat) count) -> (many (List A) out))
  (match many offset _
    ((Zero) (take-fields _ fields count))
    ((Succ k) (match many fields _ ((Nil t) (Nil _)) ((Cons t x rest) (slice-fields _ rest k count))))))

(def-fns _ $ (many repeat-field : (erased Type A) (subterm many (Nat) n) (many A v) -> (many (List A) fields))
  (match many n _ ((Zero) (Nil _)) ((Succ k) (Cons _ v (repeat-field _ k v)))))

(def-fns _ $ (many alloc-array : (erased (Hist Block) hs) (many (Store Block hs) hp)
    (many (List $ Ref Block hs) fields) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2)
    (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) v))
  (let ((many length)) (list-length _ fields))
  (let ((erased h1) (many hp1) (erased le1) (many backing)) (alloc Block _ hp (BArrayData _ fields)))
  (let ((erased h2) (many hp2) (erased le2) (many v)) (alloc Block _ hp1 (BArray _ backing 0 length)))
  (values h2 hp2 (le-trans _ _ _ le1 le2) v))

(def-fns _ $ (many array-construct : (erased (Hist Block) hs) (many (Store Block hs) hp)
    (many (Nat) index) (many (List $ Ref Block hs) fields) -> (erased (Hist Block) hs2)
    (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) v))
  (match many index _
    ((Zero) (alloc-array _ hp (Nil _)))
    ((Succ k)
      (match many fields _
        ((Nil t) (alloc Block _ hp (BError _ "array constructor arity")))
        ((Cons t head rest)
          (match many rest _
            ((Nil t2) (alloc Block _ hp (BError _ "array constructor arity")))
            ((Cons t2 tail end)
              (match many (array-view _ hp tail) _
                ((None tv) (alloc Block _ hp (BError _ "not an array")))
                ((Some tv view)
                  (let-match many view (MkArrayView _ backing offset length))
                  (alloc-array _ hp (Cons _ head (slice-fields _ (backing-fields _ hp backing) offset length))))))))))))

(def-fns _ $ (many array-destruct : (erased (Hist Block) hs) (many (Store Block hs) hp)
    (many (Ref Block hs) v) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2)
    (erased (Suffix Block hs2 hs) le) (many (Nat) index) (many (List $ Ref Block hs2) fields))
  (match many (array-view _ hp v) _
    ((None tv) (values hs hp (le-refl hs) 0 (Nil _)))
    ((Some tv view)
      (let-match many view (MkArrayView _ backing offset length))
      (match many length _
        ((Zero) (values hs hp (le-refl hs) 0 (Nil _)))
        ((Succ k)
          (match many (list-nth _ (backing-fields _ hp backing) offset) _
            ((NthMiss t fs i p) (values hs hp (le-refl hs) 0 (Nil _)))
            ((NthHit t fs i head p)
              (let ((erased h1) (many hp1) (erased le1) (many tail))
                (alloc Block _ hp (BArray _ backing (Succ offset) k)))
              (let ((erased hd1) (erased ph)) (ref-widen _ _ _ le1 head))
              (values h1 hp1 le1 1 (Cons _ (coerce head ph) (Cons _ tail (Nil _)))))))))))

(def-fns _ $ (many array-change : (erased (Hist Block) hs) (many (Store Block hs) hp)
    (many (Ref Block hs) array) (many (Nat) index) (many (Maybe $ Ref Block hs) replacement) ->
    (many (Store Block hs) hp2) (many (Maybe $ Ref Block hs) previous))
  (match many (array-view _ hp array) _
    ((None tv) (values hp (None _)))
    ((Some tv view)
      (let-match many view (MkArrayView _ backing offset length))
      (match many (nat-cmp index length) _
        ((CLt t r x y p)
          (let ((many fields)) (backing-fields _ hp backing))
          (let ((many at)) (nat-add offset index))
          (match many (list-nth _ fields at) _
            ((NthMiss _ fs i _) (values hp (None _)))
            ((NthHit _ fs i old _)
              (let ((many (Store Block hs) hp2))
                (match many replacement _
                  ((None t2) hp)
                  ((Some t2 value) (store-write Block _ hp backing (BArrayData _ (replace-field _ fields at value))))))
              (values hp2 (Some _ old)))))
        (else (values hp (None _)))))))

(def-fns _ $ (many ext-construct : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (ExtType) ext) (many (Nat) index) (many (List $ Ref Block hs) fields) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a))
  (match many ext _
    ((ExtArray) (array-construct _ hp index fields))
    ((ExtNat)
      (alloc-ext _ hp (PNat (match many index (((Nat) n))
        ((Zero) (Zero)) ((Succ k) (Succ (field-nat _ hp fields 0)))))))
    ((ExtHalf)
      (let ((many d) (erased dd)) (double (field-nat _ hp fields 0)))
      (alloc-ext _ hp (PHalf (match many index (((Nat) n))
        ((Zero) 0) ((Succ k) (match many k (((Nat) n)) ((Zero) (Succ d)) ((Succ k2) (Succ (Succ d)))))))))
    ((ExtString)
      (let ((many (String) rest)) (match many (list-nth _ fields 1) _
        ((NthHit nt nl ni x np) (heap-str _ hp x)) ((NthMiss nt nl ni np) (SNil))))
      (alloc-ext _ hp (PStr (match many index (((String) s))
        ((Zero) (SNil)) ((Succ k) (SCons (char-of-code (field-nat _ hp fields 0)) rest))))))))

(def-fns _ $ (many ext-destruct : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Payload) p) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Nat) index) (many (List $ Ref Block hs2) fields))
  (match many p _
    ((PNat n)
      (match many n _
        ((Zero) (values hs hp (le-refl hs) 0 $ Nil _))
        ((Succ k)
          (let ((erased hl2) (many hp2) (erased sf2) (many a)) $ alloc-ext _ hp $ PNat k)
          (values hl2 hp2 sf2 1 $ Cons _ a $ Nil _))))
    ((PHalf n)
      (match many (nat-halve n) _
        ((HZ) (values hs hp (le-refl hs) 0 $ Nil _))
        ((H1 m d dd)
          (let ((erased hl2) (many hp2) (erased sf2) (many a)) $ alloc-ext _ hp $ PNat m)
          (values hl2 hp2 sf2 1 $ Cons _ a $ Nil _))
        ((H2 m d dd)
          (let ((erased hl2) (many hp2) (erased sf2) (many a)) $ alloc-ext _ hp $ PNat m)
          (values hl2 hp2 sf2 2 $ Cons _ a $ Nil _))))
    ((PStr s)
      (match many s _
        ((SNil) (values hs hp (le-refl hs) 0 $ Nil _))
        ((SCons c rest)
          (let ((erased hl2) (many hp2) (erased sf2) (many a1)) $ alloc-ext _ hp $ PNat $ char-code c)
          (let ((erased hl3) (many hp3) (erased sf3) (many a2)) $ alloc-ext _ hp2 $ PStr rest)
          (let ((erased w1) (erased p1)) (ref-widen _ _ _ sf3 a1))
          (values hl3 hp3 (le-trans _ _ _ sf2 sf3) 1 $ Cons _ (coerce a1 p1) $ Cons _ a2 $ Nil _))))))


(def-fns _ $ (many tuple : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (List $ Ref Block hs) vs) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many vs _
    ((Nil a)
      (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ alloc Block _ hp $ BToken _)
      (values hl2 hp2 sf2 v))
    ((Cons a v rest)
      (match many rest _
        ((Nil b) (values hs hp (le-refl hs) v))
        ((Cons b w rest2)
          (let ((erased hl2) (many hp2) (erased sf2) (many t)) $ alloc Block _ hp $ BTup _ vs)
          (values hl2 hp2 sf2 t))))))

(def-fns _ $ (many untuple : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Nat) n) (many (Ref Block hs) v) -> (many (List $ Ref Block hs) vs))
  (match many n _
    ((Zero) (Nil _))
    ((Succ k)
      (match many k _
        ((Zero) (Cons _ v $ Nil _))
        ((Succ k2)
          (let ((erased a) (many b) (erased lt)) (store-read Block _ hp v))
          (match many b _
            ((BTup z fs) (let ((erased w2) (erased p2)) (refs-widen _ _ _ lt fs)) (coerce fs p2)) (else (Nil $ Ref Block hs))))))))

(def-fns _ $ (many ctor-fields : (erased (Hist Block) hs) (many (Store Block hs) hp)
    (many (Bool) newtype) (many (Nat) arity) (many (Ref Block hs) v) -> (many (List $ Ref Block hs) fields))
  (match many newtype _
    ((BTrue) (untuple _ hp arity v))
    ((BFalse)
      (let ((erased s) (many body) (erased sf)) (store-read Block _ hp v))
      (match many body _
        ((BTag z c fs)
          (let ((erased fs2) (erased pf)) (refs-widen _ _ _ sf fs))
          (coerce fs pf))
        (else (Nil _))))))

(def-fns _ $ (many construct : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ctor) c) (many (List $ Ref Block hs) args) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many c _
    ((MkCtor name id index arity tagged ext shape newtype)
      (match many ext _
        ((Some a e)
          (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ ext-construct _ hp e index args)
          (values hl2 hp2 sf2 v))
        ((None a)
          (match many newtype _
            ((BFalse)
              (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ alloc Block _ hp $ BTag _ c args)
              (values hl2 hp2 sf2 v))
            ((BTrue) (tuple _ hp args))))))))

; A value's discriminant and many fields where the FFI holds the type or a tag says (section 38); None
; otherwise, the value then being its fields as they stand.
(def-fns _ $ (many dispatch : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Maybe $ ExtType) ext) (many (Bool) tagged) (many (Ref Block hs) v) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Maybe $ Pair (Nat) $ List $ Ref Block hs2) r))
  (let ((erased a) (many b) (erased lt)) (store-read Block _ hp v))
  (match many b _
    ((BExt z p)
      (match many ext _
        ((None e) (values hs hp (le-refl hs) $ None _))
        ((Some e t)
          (let ((erased hs2) (many hp2) (erased le) (many i) (many fs)) $ ext-destruct _ hp p)
          (values hs2 hp2 le $ Some _ $ MkPair _ _ i fs))))
    ((BArray z backing offset _)
      (match many ext _
        ((Some t e)
          (match many e _
            ((ExtArray)
              (let ((erased h2) (many hp2) (erased le2) (many i) (many fields)) (array-destruct _ hp v))
              (values h2 hp2 le2 (Some _ (MkPair _ _ i fields))))
            (else (values hs hp (le-refl hs) (None _)))))
        ((None t) (values hs hp (le-refl hs) (None _)))))
    ((BTag z ct fs)
      (match many tagged _
        ((BTrue)
          (let ((erased w3) (erased p3)) (refs-widen _ _ _ lt fs))
          (values hs hp (le-refl hs) $ Some _ $ MkPair _ _ (ctor-index ct) (coerce fs p3)))
        ((BFalse) (values hs hp (le-refl hs) $ None _))))
    (else (values hs hp (le-refl hs) $ None _))))

(def-fns _ $ (many destruct : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ctor) c) (many (Ref Block hs) v) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Nat) i) (many (List $ Ref Block hs2) fields))
  (match many c _
    ((MkCtor name id index arity tagged ext shape newtype)
      (let ((erased hs2) (many hp2) (erased le) (many read)) $ dispatch _ hp ext tagged v)
      (match many read _
        ((Some a p) (match many p _ ((MkPair x y i fs) (values hs2 hp2 le i fs))))
        ((None a)
          (let ((erased w4) (erased p4)) (ref-widen _ _ _ le v))
          (values hs2 hp2 le index $ ctor-fields _ hp2 newtype arity (coerce v p4)))))))

(def-fns _ $ (many ctor-at : (many (Adt) adt) (many (Nat) i) -> (many (Maybe $ Ctor) c))
  (match many (list-nth _ (adt-ctors adt) i) _ ((NthHit nt nl ni c np) (Some _ c)) ((NthMiss nt nl ni np) (None _))))

(def-fns _ $ (many vnat : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Nat) n) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a))
  (alloc-ext _ hp $ PNat n))

(def-fns _
  ((many rope-walk : (subterm many (Nat) fuel) (erased (Hist Block) hs)
      (many (Store Block hs) hp) (many (Ref Block hs) r) -> (many (Rope) rope))
    (match many fuel _
      ((Zero) (REmpty))
      ((Succ k)
        (let ((erased s) (many body) (erased sf)) (store-read Block _ hp r))
        (match many body _
          ((BExt z pp) (match many pp _ ((PStr str) (RStr str)) ((PNat m) (RChar $ char-of-code m)) (else (REmpty))))
          ((BTag z ct fields)
            (let ((erased fs2) (erased pf)) (refs-widen _ _ _ sf fields))
            (rope-fields k _ hp (coerce fields pf)))
          (else (REmpty))))))
  ((many rope-fields : (subterm many (Nat) fuel) (erased (Hist Block) hs)
      (many (Store Block hs) hp) (subterm many (List $ Ref Block hs) fs) -> (many (Rope) rope))
    (match many fs _
      ((Nil t) (REmpty))
      ((Cons t f rest)
        (match many fuel _
          ((Zero) (REmpty))
          ((Succ k) (RCat (rope-walk k _ hp f) (rope-fields fuel _ hp rest))))))))

(def-fns _ $ (many flatten-value : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) r) -> (many (String) s))
  (let ((many str) (erased p)) $ flatten $ rope-walk 1000000 _ hp r)
  str)

; What an extern's implementation produces: a payload, a pair of them, or the constructor of a plain type at
; its discriminant. The dispatch below has one case per Extern and no else, so a new one has to say which.
(def-adts $ (ExtResult : -> Type)
  enum
  (many ErPayload : (many (Payload) p) -> (ExtResult))
  (many ErPair : (many (Payload) a) (many (Payload) b) -> (ExtResult))
  (many ErCtor : (many (Nat) index) -> (ExtResult))
  (many ErArrayNew : (many (Nat) length) -> (ExtResult))
  (many ErArraySwap : -> (ExtResult))
  (many ErArrayPluck : -> (ExtResult))
  (many ErArrayPlace : -> (ExtResult)))

; An extern function over its arguments (section 41). The arguments are counted against the arity here, the
; call having been checked against the model's telescope; [cs] are the constructors of the plain type it
; builds, read off that model's return type at the extern mark.
(def-fns _ $ (many apply-array-change : (erased (Hist Block) hs) (many (Store Block hs) hp)
    (many (Maybe $ Ref Block hs) array) (many (Nat) index) (many (Maybe $ Ref Block hs) replacement)
    (many (Bool) return-old) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2)
    (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r))
  (let ((many (Store Block hs) hp1) (many (Maybe $ Ref Block hs) old))
    (match many array _
      ((None t) (values hp (None _)))
      ((Some t a) (array-change _ hp a index replacement))))
  (match many old _
    ((None t)
      (let ((erased h2) (many hp2) (erased le2) (many err)) (alloc Block _ hp1 (BError _ "invalid array access")))
      (values h2 hp2 le2 (Cons _ err (Nil _))))
    ((Some t v)
      (values hs hp1 (le-refl hs) (match many return-old (((List $ Ref Block hs) r)) ((BTrue) (Cons _ v (Nil _))) ((BFalse) (Nil _)))))))

(def-fns _ $ (many apply-extern : (erased (Nat) n) (many (Extern n) e) (many (List $ Ctor) cs) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (List $ Ref Block hs) args) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r))
  (let ((many (Maybe $ Ref Block hs) a)) $ match many (list-nth _ args 0) _ ((NthHit nt nl ni x np) (Some _ x)) ((NthMiss nt nl ni np) (None _)))
  (let ((many (Maybe $ Ref Block hs) b)) $ match many (list-nth _ args 1) _ ((NthHit nt nl ni x np) (Some _ x)) ((NthMiss nt nl ni np) (None _)))
  (let ((many (Nat) na)) $ match many a _ ((Some t x) (heap-nat _ hp x)) ((None t) 0))
  (let ((many (Nat) nb)) $ match many b _ ((Some t x) (heap-nat _ hp x)) ((None t) 0))
  (let ((many (String) sa)) $ match many a _ ((Some t x) (heap-str _ hp x)) ((None t) (SNil)))
  (let ((many (String) sb)) $ match many b _ ((Some t x) (heap-str _ hp x)) ((None t) (SNil)))
  (let ((many (ExtResult) res))
    (match many e _
      ((ExArrayNew) (ErArrayNew na))
      ((ExArraySwap) (ErArraySwap))
      ((ExArrayPluck) (ErArrayPluck))
      ((ExArrayPlace) (ErArrayPlace))
      ((ExAdd) (ErPayload $ PNat $ nat-add na nb))
      ((ExSub)
        (match many (lt-dec nb (Succ na)) (((ExtResult) w))
          ((Yes x y le) (let ((many c) (erased pf)) $ sub na nb le) (ErPayload $ PNat c))
          ((No x y q) (ErPayload $ PStr "sub: negative result"))))
      ((ExMul) (ErPayload $ PNat $ nat-mul na nb))
      ((ExDiv)
        (match many (lt-dec (Zero) nb) (((ExtResult) w))
          ((Yes x y pos) (let ((many d) (erased m) (erased r) (erased mm) (erased ad) (erased p)) $ div na nb pos) (ErPayload $ PNat d))
          ((No x y q) (ErPayload $ PStr "div: zero divisor"))))
      ((ExNatCmp) (ErCtor $ cmp-index _ _ _ _ $ nat-cmp na nb))
      ((ExStrCmp) (ErCtor $ cmp-index _ _ _ _ $ str-cmp sa sb))
      ((ExNatHalve) (ErPayload $ PHalf na))
      ((ExStrLength) (let ((many n) (erased lp)) (str-length sa)) (ErPayload $ PNat n))
      ((ExNatStr) (ErPayload $ PStr $ nat-str na))
      ((ExNatMod)
        (match many (lt-dec (Zero) nb) (((ExtResult) w))
          ((Yes x y pos) (let ((many m) (erased pf) (erased pq)) $ nat-mod na nb pos) (ErPayload $ PNat m))
          ((No x y q) (ErPayload $ PStr "nat-mod: zero modulus"))))
      ((ExTrim) (ErPayload $ PStr $ trim sa))
      ((ExAppend) (ErPayload $ PStr $ str-append sa sb))
      ((ExFlatten) (ErPayload $ PStr $ match many a (((String) r)) ((Some t x) (flatten-value _ hp x)) ((None t) (SNil))))
      ((ExStrSplit)
        (let ((many len) (erased l)) $ str-length sa)
        (match many (lt-dec nb (Succ len)) (((ExtResult) w))
          ((Yes x y le)
            (let ((many a1) (many b1) (erased p) (erased la)) $ str-split sa nb len l le)
            (ErPair (PStr a1) (PStr b1)))
          ((No x y q) (ErPayload $ PStr "str-split: past the end"))))
      ((ExDivmod)
        (match many (lt-dec (Zero) nb) (((ExtResult) w))
          ((Yes x y pos)
            (let ((many qq) (many rr) (erased m) (erased mm) (erased ad) (erased pr)) $ divmod na nb pos)
            (ErPair (PNat qq) (PNat rr)))
          ((No x y q) (ErPayload $ PStr "divmod: zero divisor"))))))
  (match many res _
    ((ErArrayNew length)
      (let ((erased h1) (many hp1) (erased le1) (many blank)) (alloc Block _ hp (BToken _)))
      (let ((erased h2) (many hp2) (erased le2) (many array)) (alloc-array _ hp1 (repeat-field _ length blank)))
      (values h2 hp2 (le-trans _ _ _ le1 le2) (Cons _ array (Nil _))))
    ((ErArrayPluck) (apply-array-change _ hp a nb (None _) (BTrue)))
    ((ErArraySwap)
      (let ((many replacement)) (match many (list-nth _ args 2) (((Maybe $ Ref Block hs) r))
        ((NthHit t fs i x p) (Some _ x)) ((NthMiss t fs i p) (None _))))
      (apply-array-change _ hp a nb replacement (BTrue)))
    ((ErArrayPlace)
      (let ((many replacement)) (match many (list-nth _ args 2) (((Maybe $ Ref Block hs) r))
        ((NthHit t fs i x p) (Some _ x)) ((NthMiss t fs i p) (None _))))
      (apply-array-change _ hp a nb replacement (BFalse)))
    ((ErPayload p)
      (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ alloc-ext _ hp p)
      (values hl2 hp2 sf2 $ Cons _ v $ Nil _))
    ((ErPair p q)
      (let ((erased hl2) (many hp2) (erased sf2) (many v1)) $ alloc-ext _ hp p)
      (let ((erased hl3) (many hp3) (erased sf3) (many v2)) $ alloc-ext _ hp2 q)
      (let ((erased w1) (erased pw1)) (ref-widen _ _ _ sf3 v1))
      (values hl3 hp3 (le-trans _ _ _ sf2 sf3) $ Cons _ (coerce v1 pw1) $ Cons _ v2 $ Nil _))
    ((ErCtor i)
      (match many (list-nth _ cs i) _
        ((NthMiss nt nl ni np)
          (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ alloc Block _ hp $ BError _ "the extern implementation has no constructor to build its result with")
          (values hl2 hp2 sf2 $ Cons _ v $ Nil _))
        ((NthHit nt nl ni c np)
          (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ construct _ hp c $ Nil _)
          (values hl2 hp2 sf2 $ Cons _ v $ Nil _))))))

; ---- Values at every position of a code's index (ASSUMPTIONS 125): a code's values are the list of its
; many results, with a Picked reading them back against the index. Nothing converts between the two
; representations along a call, which is what lets a call in tail position compile to one (section 9).

(def-fns _ $ (many vals-of : (erased (Hist Block) hs) (subterm many (List $ Mult) ms) (many (Ref Block hs) v) -> (many (List $ Ref Block hs) r) (erased (Picked (Ref Block hs) ms r) pk))
  (match many ms _
    ((Nil a) (values (Nil _) (PkNil _)))
    ((Cons a m rest)
      (let ((many r) (erased pk)) $ vals-of _ rest v)
      (match many m _
        ((Many) (values (Cons _ v r) (PkMany _ rest v r pk)))
        ((Once) (values (Cons _ v r) (PkOnce _ rest v r pk)))
        ((Erased) (values r (PkErased _ rest r pk)))))))

(def-fns _ $ (many error-vals : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (List $ Mult) ms) (many (String) msg) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (erased (Picked (Ref Block hs2) ms vs) pk))
  (let ((erased hl2) (many hp2) (erased sf2) (many e)) $ alloc Block _ hp $ BError _ msg)
  (let ((many vs) (erased pk)) $ vals-of _ ms e)
  (values hl2 hp2 sf2 vs pk))

; Cut or padded to the index, a closure's arity being a runtime property; a missing value is an error block.
(def-fns _ $ (many vals-fit : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Mult) ms) (many (List $ Ref Block hs) vs) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r) (erased (Picked (Ref Block hs2) ms r) pk))
  (match many ms _
    ((Nil a) (values hs hp (le-refl hs) (Nil _) (PkNil _)))
    ((Cons a m rest)
      (match many m _
        ((Erased)
          (let ((erased hs2) (many hp2) (erased le) (many r) (erased pk)) $ vals-fit _ hp rest vs)
          (values hs2 hp2 le r (PkErased _ rest r pk)))
        ((Many)
          (match many vs _
            ((Nil b)
              (let ((erased hl2) (many hp2) (erased sf2) (many e)) $ alloc Block _ hp $ BError _ "arity mismatch")
              (let ((erased hs3) (many hp3) (erased le3) (many r) (erased pk)) $ vals-fit _ hp2 rest $ Nil _)
              (let ((erased we1) (erased pe1)) (ref-widen _ _ _ le3 e))
              (let ((many e2)) (coerce e pe1))
              (values hs3 hp3 (le-trans _ _ _ sf2 le3) (Cons _ e2 r) (PkMany _ rest e2 r pk)))
            ((Cons b v vrest)
              (let ((erased hs2) (many hp2) (erased le) (many r) (erased pk)) $ vals-fit _ hp rest vrest)
              (let ((erased wv1) (erased pv1)) (ref-widen _ _ _ le v))
              (let ((many v2)) (coerce v pv1))
              (values hs2 hp2 le (Cons _ v2 r) (PkMany _ rest v2 r pk)))))
        ((Once)
          (match many vs _
            ((Nil b)
              (let ((erased hl2) (many hp2) (erased sf2) (many e)) $ alloc Block _ hp $ BError _ "arity mismatch")
              (let ((erased hs3) (many hp3) (erased le3) (many r) (erased pk)) $ vals-fit _ hp2 rest $ Nil _)
              (let ((erased we1) (erased pe1)) (ref-widen _ _ _ le3 e))
              (let ((many e2)) (coerce e pe1))
              (values hs3 hp3 (le-trans _ _ _ sf2 le3) (Cons _ e2 r) (PkOnce _ rest e2 r pk)))
            ((Cons b v vrest)
              (let ((erased hs2) (many hp2) (erased le) (many r) (erased pk)) $ vals-fit _ hp rest vrest)
              (let ((erased wv1) (erased pv1)) (ref-widen _ _ _ le v))
              (let ((many v2)) (coerce v pv1))
              (values hs2 hp2 le (Cons _ v2 r) (PkOnce _ rest v2 r pk)))))))))

; The one value of a size-one code: the Picked refutes an empty list.
(def-fns _ $ (many vals-one : (erased (Hist Block) hs) (many (List $ Ref Block hs) vs) (erased (Picked (Ref Block hs) many-one vs) pk) -> (many (Ref Block hs) v))
  (match many vs _
    ((Cons a x rest) x)
    ((Nil a) (match erased pk (((Ref Block hs) v))))))

; A branch's fields or a closure's arguments bound to their ids, cut or padded to their count.
(def-fns _ $ (many fit-addrs : (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Nat) ids) (many (List $ Ref Block hs) vs) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r) (erased (Lockstep (Nat) (Ref Block hs2) ids r) lk))
  (match many ids _
    ((Nil a) (values hs hp (le-refl hs) (Nil _) (LsNil _ _)))
    ((Cons a x rest)
      (match many vs _
        ((Nil b)
          (let ((erased hl2) (many hp2) (erased sf2) (many e)) $ alloc Block _ hp $ BError _ "arity mismatch")
          (let ((erased hs3) (many hp3) (erased le3) (many r) (erased lk)) $ fit-addrs _ hp2 rest $ Nil _)
          (let ((erased we2) (erased pe2)) (ref-widen _ _ _ le3 e))
          (let ((many e2)) (coerce e pe2))
          (values hs3 hp3 (le-trans _ _ _ sf2 le3) (Cons _ e2 r) (LsCons _ _ x e2 rest r lk)))
        ((Cons b v vrest)
          (let ((erased hs2) (many hp2) (erased le) (many r) (erased lk)) $ fit-addrs _ hp rest vrest)
          (let ((erased wv2) (erased pv2)) (ref-widen _ _ _ le v))
          (let ((many v2)) (coerce v pv2))
          (values hs2 hp2 le (Cons _ v2 r) (LsCons _ _ x v2 rest r lk)))))))

(def-fns _ $ (many at-index : (erased (Nat) x) (erased (List $ Nat) f) (subterm many (At x f) p) -> (many (Nat) i))
  (match many p _ ((AtHere y rest) 0) ((AtThere y z rest q) (Succ $ at-index _ _ q))))

; A variable's value: from a frame of values by its place, or, in a group's frame, the member's closure
; made over the group's block.
(def-fns _ $ (many frames-get : (erased (Nat) x) (erased (List $ List $ Nat) ctx) (subterm many (Mem x ctx) p) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Frames (Ref Block hs) ctx) env) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many p _
    ((MHere y f c q)
      (match many env _
        ((FrVals a c2 f2 vs lk rest)
          (let ((many v) (erased sq)) $ at-get _ _ _ q vs lk)
          (values hs hp (le-refl hs) v))
        ((FrGroup a c2 gids g rest)
          (let ((many i)) $ at-index _ _ q)
          (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ alloc Block _ hp $ BFn _ g i $ list-nth-or _ gids i (Zero))
          (values hl2 hp2 sf2 v))))
    ((MThere y f c q)
      (match many env _
        ((FrVals a c2 f2 vs lk rest) (frames-get _ _ q _ hp rest))
        ((FrGroup a c2 gids g rest) (frames-get _ _ q _ hp rest))))))

(def-fns _ $ (many has-branch : (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) i) -> (many (Bool) r))
  (match many bs _
    ((Nil a) (BFalse))
    ((Cons a b rest) (match many b _ ((MkBranch c n0 d ids body) (or (nat-eq d i) $ has-branch _ _ rest i))))))

(def-fns _
  ((many eval : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (erased (List $ List $ Nat) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (St hs ctx) st) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (erased (Picked (Ref Block hs2) ms vs) pk))
    (match many code _
      ((CVar c x p)
        (match many st _
          ((MkSt a cx cs env)
            (let ((erased h2) (many hp2) (erased le) (many v)) $ frames-get _ _ p _ hp env)
            (values h2 hp2 le (Cons _ v $ Nil _) (PkMany _ _ v (Nil _) $ PkNil _)))))
      ((CConst c x)
        (match many (idmap-get _ x $ st-consts _ _ st) _
          ((Hit ht hk hm info hq)
            (match many info _
              ((MkEInfo z n m s mi me)
                (match many s _
                  ((SConst z2 v) (values hs hp (le-refl hs) (Cons _ v $ Nil _) (PkMany _ _ v (Nil _) $ PkNil _)))
                  ((SDyn z2) (error-vals _ hp many-one "a Dyn constant"))))))
          ((Miss ht hk hm hq) (error-vals _ hp many-one "unbound constant"))))
      ((CValue c v)
        (let ((erased wv3) (erased pv3)) (block-widen _ _ (empty-suffix _ hs) v))
        (let ((erased hl2) (many hp2) (erased sf2) (many a)) $ alloc Block _ hp (coerce v pv3))
        (values hl2 hp2 sf2 (Cons _ a $ Nil _) (PkMany _ _ a (Nil _) $ PkNil _)))
      ((CErased c ms2)
        (let ((erased hl2) (many hp2) (erased sf2) (many a)) $ alloc Block _ hp $ BToken _)
        (let ((many vs) (erased pk)) $ vals-of _ ms2 a)
        (values hl2 hp2 sf2 vs pk))
      ((CValues c ms2 cs2 pk) (eval-picked fuel _ hp _ cs2 ms2 pk st))
      ((CApp c ms2 f args cc)
        (let ((erased h1) (many hp1) (erased le1) (many fvs) (erased fpk)) $ eval fuel _ hp _ _ f st)
        (let ((many fv0)) $ vals-one _ fvs fpk)
        (let ((erased ws1) (erased ps1)) (st-widen _ _ le1 _ st))
        (let ((erased h2) (many hp2) (erased le2) (many avs)) $ eval-list fuel _ hp1 _ args (coerce st ps1))
        (let ((erased wf0) (erased pf0)) (ref-widen _ _ _ le2 fv0))
        (let ((many fv)) (coerce fv0 pf0))
        (match many fuel _
          ((Zero)
            (let ((erased h3) (many hp3) (erased le3) (many r) (erased rpk)) $ error-vals _ hp2 ms2 "out of fuel")
            (values h3 hp3 (le-trans _ _ _ (le-trans _ _ _ le1 le2) le3) r rpk))
          ((Succ k)
            (let ((many cs0)) $ st-consts _ _ st)
            (let ((erased wc0) (erased pc0)) (entries-widen _ _ (le-trans _ _ _ le1 le2) cs0))
            (let ((erased h3) (many hp3) (erased le3) (many r) (erased rpk)) $ apply k _ hp2 (coerce cs0 pc0) fv avs ms2)
            (values h3 hp3 (le-trans _ _ _ (le-trans _ _ _ le1 le2) le3) r rpk))))
      ((CLet c ms2 ns ids pk rhs rest)
        (let ((erased h1) (many hp1) (erased le1) (many vs) (erased vpk)) $ eval fuel _ hp _ _ rhs st)
        (let ((erased lk)) (picked-lockstep _ _ _ _ _ pk vpk))
        (let ((erased ws2) (erased ps2)) (st-widen _ _ le1 _ st))
        (let ((erased h2) (many hp2) (erased le2) (many r) (erased rpk)) $ eval fuel _ hp1 _ _ rest $ st-push _ _ (coerce st ps2) ids vs lk)
        (values h2 hp2 (le-trans _ _ _ le1 le2) r rpk))
      ((CLetRec c ns gids g rest)
        (match many st _
          ((MkSt a cx cs env)
            (match many g _
              ((MkGroup c1 ids fns lk)
                (let ((erased hl1) (many hp1) (erased sf1) (many ga)) $ alloc Block _ hp $ BGroup _ _ _ g env)
                (let ((erased le1)) sf1)
                (let ((erased wc1) (erased pc1)) (entries-widen _ _ le1 cs))
                (let ((erased wn1) (erased pn1)) (frames-widen _ _ le1 _ env))
                (let ((erased h2) (many hp2) (erased le2) (many r) (erased rpk)) $ eval fuel _ hp1 _ _ rest $ MkSt _ _ (coerce cs pc1) (FrGroup _ _ ids ga (coerce env pn1)))
                (values h2 hp2 (le-trans _ _ _ le1 le2) r rpk))))))
      ((CMatch c ns scrut shape branches dfl live)
        (let ((erased h1) (many hp1) (erased le1) (many svs) (erased spk)) $ eval fuel _ hp _ _ scrut st)
        (let ((many v)) $ vals-one _ svs spk)
        (let ((erased ws3) (erased ps3)) (st-widen _ _ le1 _ st))
        (let ((many st1)) (coerce st ps3))
        (let ((erased (Hist Block) h2) (many (Store Block h2) hp2) (erased (Suffix Block h2 h1) le2) (many (Maybe $ Pair (Nat) $ List $ Ref Block h2) read))
          (match many shape _
            ((ShKnown c2 adt) (dispatch _ hp1 (adt-ext adt) (adt-tagged adt) v))
            ((ShNone c2) (values h1 hp1 (le-refl h1) $ None _))
            ((ShHeld c2 mcode held)
              (let ((erased h1b) (many hp1b) (erased le1b) (many mvs) (erased mpk)) $ eval fuel _ hp1 _ _ mcode st1)
              (let ((many mref)) $ vals-one _ mvs mpk)
              (let ((erased ma) (many mb) (erased mlt)) (store-read Block _ hp1b mref))
              (match many mb (((Hist Block) h) ((Store Block h) p) ((Suffix Block h h1) l) ((Maybe $ Pair (Nat) $ List $ Ref Block h) r))
                ((BMat z a)
                  (let ((erased wv4) (erased pv4)) (ref-widen _ _ _ le1b v))
                  (let ((erased h1c) (many hp1c) (erased le1c) (many r)) $ dispatch _ hp1b (adt-ext a) (adt-tagged held) (coerce v pv4))
                  (values h1c hp1c (le-trans _ _ _ le1b le1c) r))
                (else (values h1b hp1b le1b $ None _))))))
        (let ((erased ws4) (erased ps4)) (st-widen _ _ le2 _ st1))
        (let ((many st2)) (coerce st1 ps4))
        (let ((erased wv5) (erased pv5)) (ref-widen _ _ _ le2 v))
        (let ((many v2)) (coerce v pv5))
        (let ((erased (Hist Block) h3) (many (Store Block h3) hp3) (erased (Suffix Block h3 h2) le3) (many (List $ Ref Block h3) r) (erased (Picked (Ref Block h3) ns r) rpk))
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
                      (let ((erased h2b) (many hp2b) (erased le2b) (many fs) (erased lk)) $ fit-addrs _ hp2 ids $ ctor-fields _ hp2
                        (match many shape (((Bool) _)) ((ShKnown cx adt) (adt-newtype adt)) ((ShHeld cx mc adt) (adt-newtype adt)) ((ShNone cx) (BTrue)))
                        (list-length _ ids) v2)
                      (let ((erased ws5) (erased ps5)) (st-widen _ _ le2b _ st2))
                      (let ((erased h2c) (many hp2c) (erased le2c) (many r) (erased rpk)) $ eval fuel _ hp2b _ _ body $ st-push _ _ (coerce st2 ps5) ids fs lk)
                      (values h2c hp2c (le-trans _ _ _ le2b le2c) r rpk))))))))
        (values h3 hp3 (le-trans _ _ _ (le-trans _ _ _ le1 le2) le3) r rpk))
      ((CCellAlloc c ctor slots)
        (let ((erased h1) (many hp1) (erased le1) (many fs)) (eval-list fuel _ hp _ slots st))
        (let ((erased h2) (many hp2) (erased le2) (many v)) (alloc Block _ hp1 (BTag _ ctor fs)))
        (values h2 hp2 (le-trans _ _ _ le1 le2) (Cons _ v (Nil _)) (PkMany _ _ v (Nil _) (PkNil _))))
      ((CCellWrite c k2 cell slots)
        (let ((erased h1) (many hp1) (erased le1) (many cvs) (erased cpk)) (eval fuel _ hp _ _ cell st))
        (let ((many cv)) (vals-one _ cvs cpk))
        (let ((erased st1) (erased pst)) (st-widen _ _ le1 _ st))
        (let ((erased h2) (many hp2) (erased le2) (many indices) (many vals))
          (eval-updates fuel _ hp1 _ slots (coerce st pst)))
        (let ((erased cv2) (erased pcv)) (ref-widen _ _ _ le2 cv))
        (let ((many target)) (coerce cv pcv))
        (let ((erased s) (many body) (erased sf)) (store-read Block _ hp2 target))
        (let ((erased (Hist Block) h3) (many (Store Block h3) hp3) (erased (Suffix Block h3 h2) le3)
            (many (List $ Ref Block h3) vs) (erased (Picked (Ref Block h3) many-one vs) pk))
          (match many body _
            ((BTag z ctor fields)
              (let ((erased fs2) (erased pf)) (refs-widen _ _ _ sf fields))
              (let ((many hp3)) (store-write Block _ hp2 target (BTag _ ctor (replace-fields _ (coerce fields pf) indices vals))))
              (values h2 hp3 (le-refl h2) (Cons _ target (Nil _)) (PkMany _ _ target (Nil _) (PkNil _))))
            (else (error-vals _ hp2 many-one "not a cell"))))
        (values h3 hp3 (le-trans _ _ _ (le-trans _ _ _ le1 le2) le3) vs pk))
      ((CCellRead c k2 index cell)
        (let ((erased h1) (many hp1) (erased le1) (many cvs) (erased cpk)) (eval fuel _ hp _ _ cell st))
        (let ((many cv)) (vals-one _ cvs cpk))
        (let ((erased s) (many body) (erased sf)) (store-read Block _ hp1 cv))
        (let ((erased (Hist Block) h2) (many (Store Block h2) hp2) (erased (Suffix Block h2 h1) le2)
            (many (List $ Ref Block h2) vs) (erased (Picked (Ref Block h2) many-one vs) pk))
          (match many body _
            ((BTag z ctor fields)
              (match many (list-nth _ fields index) _
                ((NthHit t fs i v p)
                  (let ((erased v2) (erased pv)) (ref-widen _ _ _ sf v))
                  (let ((many out)) (coerce v pv))
                  (values h1 hp1 (le-refl h1) (Cons _ out (Nil _)) (PkMany _ _ out (Nil _) (PkNil _))))
                ((NthMiss t fs i p) (error-vals _ hp1 many-one "cell field out of range"))))
            (else (error-vals _ hp1 many-one "not a cell"))))
        (values h2 hp2 (le-trans _ _ _ le1 le2) vs pk))
      ((CAbsurd c ms2) (error-vals _ hp ms2 "absurd code reached"))
      ((CError c ms2 m) (error-vals _ hp ms2 m))))

  ((many eval-list : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (many (St hs ctx) st) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs))
    (match many cs _
      ((Nil a) (values hs hp (le-refl hs) $ Nil _))
      ((Cons a c rest)
        (let ((erased h1) (many hp1) (erased le1) (many vs1) (erased pk1)) $ eval fuel _ hp _ _ c st)
        (let ((many vo1)) $ vals-one _ vs1 pk1)
        (let ((erased ws6) (erased ps6)) (st-widen _ _ le1 _ st))
        (let ((erased h2) (many hp2) (erased le2) (many vs)) $ eval-list fuel _ hp1 _ rest (coerce st ps6))
        (let ((erased wo1) (erased po1)) (ref-widen _ _ _ le2 vo1))
        (values h2 hp2 (le-trans _ _ _ le1 le2) $ Cons _ (coerce vo1 po1) vs))))

  ((many eval-updates : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp)
      (erased (List $ List $ Nat) ctx) (subterm many (List $ Pair (Nat) $ Code ctx many-one) slots)
      (many (St hs ctx) st) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2)
      (erased (Suffix Block hs2 hs) le) (many (List $ Nat) indices) (many (List $ Ref Block hs2) vals))
    (match many slots _
      ((Nil a) (values hs hp (le-refl hs) (Nil _) (Nil _)))
      ((Cons a slot rest)
        (let-match many slot (MkPair x y i code))
        (let ((erased h1) (many hp1) (erased le1) (many vs) (erased pk)) (eval fuel _ hp _ _ code st))
        (let ((many v)) (vals-one _ vs pk))
        (let ((erased st1) (erased pst)) (st-widen _ _ le1 _ st))
        (let ((erased h2) (many hp2) (erased le2) (many indices) (many vals))
          (eval-updates fuel _ hp1 _ rest (coerce st pst)))
        (let ((erased v2) (erased pv)) (ref-widen _ _ _ le2 v))
        (values h2 hp2 (le-trans _ _ _ le1 le2) (Cons _ i indices) (Cons _ (coerce v pv) vals)))))

  ((many eval-picked : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (erased (List $ List $ Nat) ctx) (subterm many (List $ Code ctx many-one) cs) (subterm many (List $ Mult) ms) (erased (Picked (Code ctx many-one) ms cs) pk) (many (St hs ctx) st) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (erased (Picked (Ref Block hs2) ms vs) rpk))
    (match many ms _
      ((Nil a) (values hs hp (le-refl hs) (Nil _) (PkNil _)))
      ((Cons a m rest)
        (match many m _
          ((Many)
            (let-match erased pk (PkMany ta ms2 c0 cs2 p))
            (let-match many cs (Cons b c crest))
            (let ((erased h1) (many hp1) (erased le1) (many vs1) (erased pk1)) $ eval fuel _ hp _ _ c st)
            (let ((many vo1)) $ vals-one _ vs1 pk1)
            (let ((erased ws7) (erased ps7)) (st-widen _ _ le1 _ st))
            (let ((erased h2) (many hp2) (erased le2) (many vs) (erased rpk)) $ eval-picked fuel _ hp1 _ crest rest p (coerce st ps7))
            (let ((erased wo2) (erased po2)) (ref-widen _ _ _ le2 vo1))
            (let ((many vo)) (coerce vo1 po2))
            (values h2 hp2 (le-trans _ _ _ le1 le2) (Cons _ vo vs) (PkMany _ rest vo vs rpk)))
          ((Once)
            (let-match erased pk (PkOnce ta ms2 c0 cs2 p))
            (let-match many cs (Cons b c crest))
            (let ((erased h1) (many hp1) (erased le1) (many vs1) (erased pk1)) $ eval fuel _ hp _ _ c st)
            (let ((many vo1)) $ vals-one _ vs1 pk1)
            (let ((erased ws7) (erased ps7)) (st-widen _ _ le1 _ st))
            (let ((erased h2) (many hp2) (erased le2) (many vs) (erased rpk)) $ eval-picked fuel _ hp1 _ crest rest p (coerce st ps7))
            (let ((erased wo2) (erased po2)) (ref-widen _ _ _ le2 vo1))
            (let ((many vo)) (coerce vo1 po2))
            (values h2 hp2 (le-trans _ _ _ le1 le2) (Cons _ vo vs) (PkOnce _ rest vo vs rpk)))
          ((Erased)
            (let-match erased pk (PkErased ta ms2 cs2 p))
            (let ((erased h2) (many hp2) (erased le2) (many vs) (erased rpk)) $ eval-picked fuel _ hp _ cs rest p st)
            (values h2 hp2 le2 vs (PkErased _ rest vs rpk)))))))

  ((many eval-branch : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (erased (List $ List $ Nat) ctx) (many (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) i) (many (List $ Ref Block hs) fields) (many (St hs ctx) st) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (erased (Picked (Ref Block hs2) ns vs) pk))
    (match many bs _
      ((Nil a) (error-vals _ hp ns $ str-cat "no branch for discriminant " $ nat-str i))
      ((Cons a b rest)
        (match many b _
          ((MkBranch c n0 d ids body)
            (match many (nat-cmp d i) _
              ((CEq eq-t eq-r eq-x)
                (let ((erased h1) (many hp1) (erased le1) (many fs) (erased lk)) $ fit-addrs _ hp ids fields)
                (let ((erased ws8) (erased ps8)) (st-widen _ _ le1 _ st))
                (let ((erased h2) (many hp2) (erased le2) (many r) (erased rpk)) $ eval fuel _ hp1 _ _ body $ st-push _ _ (coerce st ps8) ids fs lk)
                (values h2 hp2 (le-trans _ _ _ le1 le2) r rpk))
              (else (eval-branch fuel _ hp _ ns rest i fields st))))))))

  ; A closure is a member of the group at its block: the body runs over the parameters, the group's frame
  ; and the frames the group closed over. A missing member is an error block (ASSUMPTIONS 127). The call
  ; site's index and the member's returns are reconciled before the body runs, not after, so the body's
  ; values are the call's own and the call to eval is a tail call (section 9).
  ((many apply : (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) cs) (many (Ref Block hs) f) (many (List $ Ref Block hs) args) (many (List $ Mult) ms) ->
      (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (erased (Picked (Ref Block hs2) ms vs) pk))
    (let ((erased fa) (many fb) (erased flt)) (store-read Block _ hp f))
    (match many fb _
      ((BFn z ga i id)
        (let ((erased wg1) (erased pg1)) (ref-widen _ _ _ flt ga))
        (let ((many g)) (coerce ga pg1))
        (let ((erased gn) (many gb) (erased glt)) (store-read Block _ hp g))
        (match many gb _
          ((BGroup z2 gids ctx group cenv)
            (match many group _
              ((MkGroup c ids fns lk)
                (match many (list-nth _ fns i) _
                  ((NthMiss nt nl ni np) (error-vals _ hp ms "no such member"))
                  ((NthHit nt nl ni p np)
                    (match many p _
                      ((MkPair x y _ fn)
                        (match many fn _
                          ((MkFunc gg cc rets name fid params body impl top)
                            (match many impl _
                              ((Some a im)
                                (match many im _
                                  ((MkImpl se ecs)
                                    (match many se _
                                      ((MkSomeExtern n e)
                                        (let ((erased h1) (many hp1) (erased le1) (many r)) $ apply-extern _ e ecs _ hp args)
                                        (let ((erased h2) (many hp2) (erased le2) (many r2) (erased pk2)) $ vals-fit _ hp1 ms r)
                                        (values h2 hp2 (le-trans _ _ _ le1 le2) r2 pk2))))))
                              ((None a)
                                (match many fuel _
                                  ((Zero) (error-vals _ hp ms "out of fuel"))
                                  ((Succ k)
                                    (let ((erased h2) (many hp2) (erased le2) (many vs) (erased lkp)) $ fit-addrs _ hp params args)
                                    (let ((erased wg2) (erased pg2)) (ref-widen _ _ _ le2 g))
                                    (let ((erased wn2) (erased pn2)) (frames-widen _ _ (le-trans _ _ _ glt le2) _ cenv))
                                    (let ((many env)) $ FrVals _ _ params vs lkp $ FrGroup _ _ ids (coerce g pg2) (coerce cenv pn2))
                                    (let ((erased wc2) (erased pc2)) (entries-widen _ _ le2 cs))
                                    (match many (mults-same rets ms) _
                                      ((None b)
                                        (let ((erased h3) (many hp3) (erased le3) (many r) (erased rpk)) $ error-vals _ hp2 ms "arity mismatch")
                                        (values h3 hp3 (le-trans _ _ _ le2 le3) r rpk))
                                      ((Some b same)
                                        (let ((erased h3) (many hp3) (erased le3) (many r) (erased rpk)) $ eval k _ hp2 _ _ body $ MkSt _ _ (coerce cs pc2) env)
                                        (values h3 hp3 (le-trans _ _ _ le2 le3) r (picked-same _ rets ms r same rpk)))))))))))))))))
          (else (error-vals _ hp ms "not a group"))))
      ((BCtorFn z c)
        (let ((erased h2) (many hp2) (erased le2) (many v)) $ construct _ hp c args)
        (let ((erased h3) (many hp3) (erased le3) (many r) (erased rpk)) $ vals-fit _ hp2 ms $ Cons _ v $ Nil _)
        (values h3 hp3 (le-trans _ _ _ le2 le3) r rpk))
      ((BError z m) (error-vals _ hp ms m))
      (else (error-vals _ hp ms "cannot apply a value that is not a function")))))

(let ((many eval-fuel)) 1000000000)

(def-fns _ $ (many run-code : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) cs) (erased (List $ Mult) ms) (many (Code (Nil (List (Nat))) ms) code) -> (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (erased (Picked (Ref Block hs2) ms vs) pk))
  (eval eval-fuel _ hp _ _ code $ MkSt _ _ cs $ FrNil _))

; ---- Run-position statements against the environment (section 34): each reads the store out, runs or
; allocates, and puts it back with what holds its addresses widened.

(def-fns _ $ (many set-states : (erased (Hist Block) hs) (many (IdMap $ EInfo hs) en) (subterm many (List $ Nat) ids) (many (List $ Ref Block hs) vs) (erased (Lockstep (Nat) (Ref Block hs) ids vs) lk) -> (many (IdMap $ EInfo hs) r))
  (match many ids _
    ((Nil a) en)
    ((Cons a x rest)
      (let-match erased lk (LsCons ta tb x0 v0 xs vrest0 p))
      (let-match many vs (Cons b v vrest))
      (set-states _ (entries-set-state _ en x $ SConst _ v) rest vrest p))))

(def-fns _ $ (many env-run-final : (many (Env) e) (many (Code (Nil (List (Nat))) many-one) code) (many (Term) ty) -> (many (Env) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store e)
  (let ((erased hs2) (many hp2) (erased le) (many vs) (erased pk)) $ run-code _ hp en _ code)
  (let ((many en2) (many fi2)) $ store-grow _ _ le en fi)
  (env-with-store e _ hp2 en2 $ Cons _ (MkPair _ _ (vals-one _ vs pk) ty) fi2))

(def-fns _ $ (many close-members : (many (Env) e) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) en) (many (List $ Pair (Ref Block hs) $ Term) fi) (subterm many (List $ Nat) ids) (many (Ref Block hs) g) (many (Nat) i) -> (many (Env) r))
  (match many ids _
    ((Nil a) (env-with-store e _ hp en fi))
    ((Cons a x rest)
      (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ alloc Block _ hp $ BFn _ g i x)
      (let ((erased le)) sf2)
      (let ((many en2) (many fi2)) $ store-grow _ _ le en fi)
      (let ((erased wg3) (erased pg3)) (ref-widen _ _ _ le g))
      (close-members e _ hp2 (entries-set-state _ en2 x $ SConst _ v) fi2 rest (coerce g pg3) $ Succ i))))

; A run-position def-fns: the group's block over no frames, then a closure block per member.
(def-fns _ $ (many env-close-group : (many (Env) e) (erased (List $ Nat) gids) (many (Group gids (Nil (List (Nat)))) g) -> (many (Env) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store e)
  (let ((erased hl1) (many hp1) (erased sf1) (many ga)) $ alloc Block _ hp $ BGroup _ _ _ g $ FrNil _)
  (let ((many en1) (many fi1)) $ store-grow _ _ sf1 en fi)
  (match many g _ ((MkGroup c ids fns lk) (close-members e _ hp1 en1 fi1 ids ga 0))))

; The Const fields of a value bound to their ids at their declared multiplicities (section 15): a many
; field its address, an erased one the token, a missing one an error block.
(def-fns _ $ (many set-field-states : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) en) (many (List $ Pair (Ref Block hs) $ Term) fi) (subterm many (List $ Nat) fids) (many (List $ Mult) mults) (many (List $ Ref Block hs) vs) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (many (IdMap $ EInfo hs2) en2) (many (List $ Pair (Ref Block hs2) $ Term) fi2))
  (match many fids _
    ((Nil a) (values hs hp en fi))
    ((Cons a x rest)
      (let ((many (Mult) m) (many (List $ Mult) mrest)) $ match many mults _ ((Nil b) (values (Many) $ Nil _)) ((Cons b m0 mr) (values m0 mr)))
      (let ((many (Block (Ref Block hs)) filler)) $ match many m _ ((Many) (BError _ "missing value"))
        ((Once) (BError _ "missing value")) ((Erased) (BToken _)))
      (let ((many (Maybe $ Ref Block hs) have)) $ match many m _ ((Erased) (None _)) ((Many) (match many vs (((Maybe $ Ref Block hs) r)) ((Nil b) (None _)) ((Cons b v vrest) (Some _ v))))
        ((Once) (match many vs (((Maybe $ Ref Block hs) r)) ((Nil b) (None _)) ((Cons b v vrest) (Some _ v)))))
      (let ((many (List $ Ref Block hs) vrest)) $ match many m _ ((Erased) vs) ((Many) (match many vs (((List $ Ref Block hs) r)) ((Nil b) (Nil _)) ((Cons b v vr) vr)))
        ((Once) (match many vs (((List $ Ref Block hs) r)) ((Nil b) (Nil _)) ((Cons b v vr) vr))))
      (match many have _
        ((Some b v) (set-field-states _ hp (entries-set-state _ en x $ SConst _ v) fi rest mrest vrest))
        ((None b)
          (let ((erased hl2) (many hp2) (erased sf2) (many t)) $ alloc Block _ hp filler)
          (let ((erased le)) sf2)
          (let ((many en2) (many fi2)) $ store-grow _ _ le en fi)
          (let ((erased wr1) (erased pr1)) (refs-widen _ _ _ le vrest))
          (set-field-states _ hp2 (entries-set-state _ en2 x $ SConst _ t) fi2 rest mrest (coerce vrest pr1)))))))

(def-fns _ $ (many env-run-let : (many (Env) e) (many (List $ Mult) ms) (many (Code (Nil (List (Nat))) ms) code) (many (List $ Nat) ids) -> (many (Env) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store e)
  (let ((erased hs2) (many hp2) (erased le) (many vs) (erased pk)) $ run-code _ hp en _ code)
  (let ((many en2) (many fi2)) $ store-grow _ _ le en fi)
  (let ((erased hs3) (many hp3) (many en3) (many fi3)) $ set-field-states _ hp2 en2 fi2 ids ms vs)
  (env-with-store e _ hp3 en3 fi3))

; The discriminant of a Const entry's value under a constructor's reading, or None where it is no Const.
(def-fns _ $ (many env-destruct : (many (Env) e) (many (Nat) x) (many (Ctor) ct) -> (many (Env) r) (many (Maybe $ Nat) i))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store e)
  (match many (idmap-get _ x en) _
    ((Miss ht hk hm hq) (values e $ None _))
    ((Hit ht hk hm info hq)
      (match many info _
        ((MkEInfo z n m s mi me)
          (match many s _
            ((SDyn z2) (values e $ None _))
            ((SConst z2 v)
              (let ((erased hs2) (many hp2) (erased le) (many i) (many fs)) $ destruct _ hp ct v)
              (let ((many en2) (many fi2)) $ store-grow _ _ le en fi)
              (values (env-with-store e _ hp2 en2 fi2) $ Some _ i))))))))

(def-fns _ $ (many env-set-fields : (many (Env) e) (many (Nat) x) (many (Ctor) ct) (many (List $ Nat) fids) (many (List $ Mult) mults) -> (many (Env) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store e)
  (match many (idmap-get _ x en) _
    ((Miss ht hk hm hq) e)
    ((Hit ht hk hm info hq)
      (match many info _
        ((MkEInfo z n m s mi me)
          (match many s _
            ((SDyn z2) e)
            ((SConst z2 v)
              (let ((erased hs2) (many hp2) (erased le) (many i) (many fs)) $ destruct _ hp ct v)
              (let ((many en2) (many fi2)) $ store-grow _ _ le en fi)
              (let ((erased hs3) (many hp3) (many en3) (many fi3)) $ set-field-states _ hp2 en2 fi2 fids mults fs)
              (env-with-store e _ hp3 en3 fi3))))))))

; A run-position let-match: the scrutinee's code run and its fields bound (section 16).
(def-fns _ $ (many env-run-fields : (many (Env) e) (many (Code (Nil (List (Nat))) many-one) code) (many (Ctor) ct) (many (List $ Nat) fids) (many (List $ Mult) mults) -> (many (Env) r))
  (let ((erased hs) (many hp) (many en) (many fi)) $ env-store e)
  (let ((erased hs1) (many hp1) (erased le1) (many vs) (erased pk)) $ run-code _ hp en _ code)
  (let ((erased hs2) (many hp2) (erased le2) (many i) (many fs)) $ destruct _ hp1 ct $ vals-one _ vs pk)
  (let ((many en2) (many fi2)) $ store-grow _ _ (le-trans _ _ _ le1 le2) en fi)
  (let ((erased hs3) (many hp3) (many en3) (many fi3)) $ set-field-states _ hp2 en2 fi2 fids mults fs)
  (env-with-store e _ hp3 en3 fi3))

; Every binder of a run-position statement that did not run holds the token, as after an error.
(def-fns _ $ (many env-set-tokens : (many (Env) e) (subterm many (List $ Nat) ids) -> (many (Env) r))
  (match many ids _
    ((Nil a) e)
    ((Cons a x rest) (env-set-tokens (set-state-closed e x $ BToken _) rest))))
