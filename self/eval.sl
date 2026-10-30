; self/eval.sl -- the compile-time interpreter (DESIGN.md section 29's round trip; lib/eval.ml): a plain recursive
; evaluator over post-erasure code and the store of self/heap.sl, bounded by a fuel that decreases along the
; call stack so the checker accepts it. Every value is an address; every step returns the grown store with
; a proof of the growth, by which what was held before is widened. Extern functions run as the host's own
; (section 42).

(def-fns _ $ (erased le-refl : (erased (Hist Block) a) -> (erased (Suffix Block a a) p))
  (SfHere Block a))

(def-fns _ $ (erased hist-le-trans : (erased (Hist Block) a) (erased (Hist Block) b) (erased (Hist Block) c)
    (erased (Suffix Block b a) p) (erased (Suffix Block c b) q) -> (erased (Suffix Block c a) r))
  (suffix-trans Block c b a q p))

; What runs under: the Settled entries the code names and the frames it binds.
(def-adts $ (St : ((Hist Block) a) ((List $ List $ Nat) ctx) -> Type)
  enum
  (many MkSt : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (Frames (Ref Block a) ctx) env) -> (St a ctx)))

(def-fns _ $ (erased st-widen : (erased (Hist Block) b) (erased (Hist Block) c) (erased (Suffix Block c b) le)
    (erased (List $ List $ Nat) ctx) (erased (St b ctx) st) ->
    (erased (St c ctx) r) (erased (Coercible (Shared) (St b ctx) st (Shared) (St c ctx) r) p))
  (let-match erased st (MkSt _ cx env))
  (let ((erased env2) (erased pe)) (frames-widen b c le cx env))
  (values (MkSt _ _ env2) (coercible-ctor (Shared) MkSt b c cx cx pe)))

(def-fns _ $ (many st-push : (erased (Hist Block) a) (erased (List $ List $ Nat) ctx) (many (St a ctx) st) (many (List $ Nat) f) (many (List $ Ref Block a) vs) (erased (Lockstep (Nat) (Ref Block a) f vs) lk) -> (many (St a (Cons (List (Nat)) f ctx)) r))
  (match many st _ ((MkSt _ _ env) (MkSt _ _ $ FrVals _ _ f vs lk env))))

; ---- Extern values (section 42; lib/ffi_core.ml): payload blocks, read and made through the store

(def-fns _ $ (many zeros-before : (subterm many (List $ Nat) shape) (many (Nat) index) -> (many (Nat) n))
  (let-match many shape (Cons _ a rest) ((Nil _) 0))
  (let-match many index (Succ i) ((Zero) 0))
  (let ((many n)) $ notail $ zeros-before rest i)
  (let-match many a (Zero) (else n))
  (Succ n))

(def-fns _ $ (many fieldless-index : (subterm many (List $ Nat) shape) (many (Nat) k) -> (many (Nat) i))
  (let-match many shape (Cons _ a rest) ((Nil _) 0))
  (let-match many a (Zero) (else (Succ $ notail $ fieldless-index rest k)))
  (let-match many k (Succ j) ((Zero) 0))
  (Succ $ notail $ fieldless-index rest j))

(def-fns _ $ (many word-of-block : (erased Type R) (many (Block R) b) -> (many (Maybe $ Nat) w))
  (match many b _
    ((BExt _ p) (match many p _ ((PNat n) (Some _ n)) (else (None _))))
    ((BTag _ ct fs)
      (let-match many fs (Nil _) (else (None _)))
      (let-match many ct (MkCtor _ _ index _ tagged _ shape _))
      (Some _ $ match many tagged (((Nat) _)) ((BTrue) (zeros-before shape index)) ((BFalse) 0)))
    ((BToken _) (Some _ 0))
    (else (None _))))

(def-fns _ $ (many heap-nat : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (Nat) n))
  (let ((erased _) (many b) (erased _)) (hread _ hp a))
  (match many (word-of-block _ b) _ ((Some _ n) n) ((None _) 0)))

(def-fns _ $ (many heap-str : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (String) n))
  (let ((erased _) (many b) (erased _)) (hread _ hp a))
  (let-match many b (BExt _ p) (else (SNil)))
  (match many p _ ((PStr s) s) ((PBytes s) s) (else (SNil))))

(def-fns _ $ (many alloc-ext : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Payload) p) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a))
  (halloc _ hp $ BExt _ p))

(def-fns _ $ (many byte-run : (subterm many (Nat) n) (many (Char) c) -> (many (Rope) r))
  (let-match many n (Succ k) ((Zero) (REmpty)))
  (RCat (RChar c) (notail $ byte-run k c)))

(def-fns _ $ (many char-of-nat : (many (Nat) n) -> (many (Maybe $ Char) c))
  (match many (lt-dec n u8-modulus) _
    ((Yes _ _ _ _ p) (Some _ $ MkChar $ MkU8 n p))
    ((No _ _ _ _ _) (None _))))

(def-fns _ $ (many byte-at : (subterm many (String) s) (many (Nat) i) -> (many (Maybe $ Nat) b))
  (let-match many s (SCons c rest) ((SNil) (None _)))
  (match many i _ ((Zero) (Some _ $ char-code c)) ((Succ k) (tail $ byte-at rest k))))

(def-fns _ $ (many str-range : (subterm many (String) s) (many (Nat) i) (many (Nat) n) (many (Rope) acc) -> (many (Rope) r))
  (let-match many s (SCons c rest) ((SNil) acc))
  (let-match many i (Zero) ((Succ k) (tail $ str-range rest k n acc)))
  (let-match many n (Succ m) ((Zero) acc))
  (tail $ str-range rest (Zero) m $ RCat acc $ RChar c))

(def-fns _ $ (many str-splice : (many (String) s) (many (Nat) j) (many (Nat) n) (many (Rope) mid) -> (many (String) r))
  (let ((many len) (erased _)) (str-length s))
  (let ((many r) (erased _)) (flatten $ str-range s (nat-add j n) len $ RCat (str-range s (Zero) j $ REmpty) mid))
  r)

(def-fns _ $ (many list-range : (erased Type A) (subterm many (List A) xs) (many (Nat) i) (many (Nat) n) -> (many (List A) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (Nil _)))
  (let-match many i (Zero) ((Succ k) (tail $ list-range _ rest k n)))
  (let-match many n (Succ m) ((Zero) (Nil _)))
  (Cons _ x (notail $ list-range _ rest (Zero) m)))

(def-fns _ $ (many field-nat : (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ref Block hs) fields) (many (Nat) i) -> (many (Nat) n))
  (match many (list-nth _ fields i) _ ((NthHit _ _ _ x _) (heap-nat _ hp x)) ((NthMiss _ _ _ _) 0)))

(def-fns _ $ (many replace-field : (erased Type A) (subterm many (List A) fields)
    (many (Nat) index) (many A value) -> (many (List A) out))
  (let-match many fields (Cons _ x rest) ((Nil _) (Nil _)))
  (match many index _
    ((Zero) (Cons _ value rest))
    ((Succ k) (Cons _ x (notail $ replace-field _ rest k value)))))

(def-fns _ $ (many replace-fields : (erased Type A) (many (List A) fields)
    (subterm many (List $ Nat) indices) (many (List A) elems) -> (many (List A) out))
  (let-match many indices (Cons _ i rest) ((Nil _) fields))
  (match many elems _
    ((Nil _) fields)
    ((Cons _ v tail2) (tail $ replace-fields _ (replace-field _ fields i v) rest tail2))))

(def-fns _ $ (many array-elems : (erased (Hist Block) hs) (many (Heap hs) hp)
    (many (Ref Block hs) v) -> (many (Maybe $ Pair (Nat) $ IdMap $ Ref Block hs) r))
  (let ((erased _) (many body) (erased sf)) (hread _ hp v))
  (let-match many body (BArray _ n es) (else (None _)))
  (let ((erased _) (erased pe)) (idmap-widen _ _ _ sf es))
  (Some _ (MkPair _ _ n (coerce es pe))))

(def-fns _ $ (many array-fields : (erased (Hist Block) hs) (many (Heap hs) hp)
    (many (Ref Block hs) v) -> (many (Maybe $ List $ Ref Block hs) fields))
  (let-match many (array-elems _ hp v) (Some _ ne) ((None _) (None _)))
  (let-match many ne (MkPair _ _ n es))
  (Some _ (idmap-prefix _ es n (Nil _))))

(def-fns _ $ (many repeat-field : (erased Type A) (subterm many (Nat) n) (many A v) -> (many (List A) fields))
  (match many n _ ((Zero) (Nil _)) ((Succ k) (Cons _ v (notail $ repeat-field _ k v)))))

(def-fns _ $ (many array-construct : (erased (Hist Block) hs) (many (Heap hs) hp)
    (many (Nat) index) (many (List $ Ref Block hs) fields) -> (erased (Hist Block) hs2)
    (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) v))
  (let-match many index (Succ _) ((Zero) (halloc _ hp (array-block _ (Nil _)))))
  (let-match many fields (Cons _ head rest) ((Nil _) (halloc _ hp (BError _ "array constructor arity"))))
  (let-match many rest (Cons _ tail2 _) ((Nil _) (halloc _ hp (BError _ "array constructor arity"))))
  (match many (array-fields _ hp tail2) _
    ((None _) (halloc _ hp (BError _ "not an array")))
    ((Some _ fs) (halloc _ hp (array-block _ (Cons _ head fs))))))

(def-fns _ $ (many array-destruct : (erased (Hist Block) hs) (many (Heap hs) hp)
    (many (Ref Block hs) v) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2)
    (erased (Suffix Block hs2 hs) le) (many (Nat) index) (many (List $ Ref Block hs2) fields))
  (let-match many (array-fields _ hp v) (Some _ fields) ((None _) (values hs hp (le-refl hs) 0 (Nil _))))
  (let-match many fields (Cons _ head rest) ((Nil _) (values hs hp (le-refl hs) 0 (Nil _))))
  (let ((erased h1) (many hp1) (erased le1) (many tl)) (halloc _ hp (array-block _ rest)))
  (let ((erased _) (erased ph)) (ref-widen _ _ _ le1 head))
  (values h1 hp1 le1 1 (Cons _ (coerce head ph) (Cons _ tl (Nil _)))))

(def-fns _ $ (many array-change : (erased (Hist Block) hs) (many (Heap hs) hp)
    (many (Ref Block hs) array) (many (Nat) index) (many (Maybe $ Ref Block hs) replacement) ->
    (many (Heap hs) hp2) (many (Maybe $ Ref Block hs) previous))
  (let-match many (array-elems _ hp array) (Some _ ne) ((None _) (values hp (None _))))
  (let-match many ne (MkPair _ _ n es))
  (let-match many (idmap-get _ index es) (Hit _ _ _ old _) ((Miss _ _ _ _) (values hp (None _))))
  (let ((many (Heap hs) hp2))
    (match many replacement _
      ((None _) hp)
      ((Some _ value) (hwrite _ hp array (BArray _ n (idmap-set _ index value es))))))
  (values hp2 (Some _ old)))

(def-fns _ $ (many list-refs : (subterm many (Nat) fuel) (erased (Hist Block) hs)
    (many (Heap hs) hp) (many (Ref Block hs) v) -> (many (Maybe $ List $ Ref Block hs) r))
  (let-match many fuel (Succ k) ((Zero) (None _)))
  (let ((erased _) (many body) (erased sf)) (hread _ hp v))
  (let-match many body (BTag _ _ fields) (else (Some _ $ Nil _)))
  (let ((erased _) (erased pf)) (refs-widen _ _ _ sf fields))
  (let-match many (coerce fields pf) (Cons _ x more)
    (else (Some _ $ Nil _)))
  (let-match many more (Cons _ rest _) (else (Some _ $ Nil _)))
  (let-match many (notail $ list-refs k _ hp rest) (Some _ tl) ((None _) (None _)))
  (Some _ $ Cons _ x tl))

(def-fns _ $ (many cons-string : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Nat) index) (many (List $ Ref Block hs) fields) -> (many (Maybe $ String) s))
  (let-match many index (Succ _) ((Zero) (Some _ $ SNil)))
  (let ((many (String) rest)) (match many (list-nth _ fields 1) _
    ((NthHit _ _ _ x _) (heap-str _ hp x)) ((NthMiss _ _ _ _) (SNil))))
  (let-match many (char-of-nat $ field-nat _ hp fields 0) (Some _ c) ((None _) (None _)))
  ;! suppress warn SCons the program being run asked for this cons
  (Some _ $ SCons c rest))
;! restore warn SCons

(def-fns _ $ (many alloc-payloads : (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (List $ Payload) ps) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) rs))
  (let-match many ps (Cons _ p rest) ((Nil _) (values hs hp (le-refl hs) $ Nil _)))
  (let ((erased _) (many hp1) (erased s1) (many a)) $ alloc-ext _ hp p)
  (let ((erased h2) (many hp2) (erased s2) (many rs)) $ notail $ alloc-payloads _ hp1 rest)
  (let ((erased _) (erased pw)) (ref-widen _ _ _ s2 a))
  (values h2 hp2 (hist-le-trans _ _ _ s1 s2) $ Cons _ (coerce a pw) rs))

(def-fns _ $ (many pos-block : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ctor) nopos) (many (Ctor) mkpos) (many (String) file) (many (Spot) p) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) a))
  (let-match many (spot-pos file p) (MkPos f l c) ((NoPos) (halloc _ hp $ BTag _ nopos $ Nil _)))
  (let ((erased _) (many hp1) (erased s1) (many rs)) $ alloc-payloads _ hp $ Cons _ (PStr f) $ Cons _ (PNat l) $ Cons _ (PNat c) $ Nil _)
  (let ((erased h2) (many hp2) (erased s2) (many a)) $ halloc _ hp1 $ BTag _ mkpos rs)
  (values h2 hp2 (hist-le-trans _ _ _ s1 s2) a))

(def-fns _ $ (many raw-list : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ctor) nil) (many (Ctor) cons) (many (String) file) (subterm many (List $ Syn) xs) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) a))
  (let-match many xs (Cons _ x rest) ((Nil _) (halloc _ hp $ BTag _ nil $ Nil _)))
  (let ((erased _) (many hp1) (erased s1) (many tl)) $ notail $ raw-list _ hp nil cons file rest)
  (let ((erased _) (many hp2) (erased s2) (many hd)) $ alloc-ext _ hp1 $ PRaw file x)
  (let ((erased _) (erased pw)) (ref-widen _ _ _ s2 tl))
  (let ((erased h3) (many hp3) (erased s3) (many c)) $ halloc _ hp2 $ BTag _ cons $ Cons _ hd $ Cons _ (coerce tl pw) $ Nil _)
  (values h3 hp3 (hist-le-trans _ _ _ (hist-le-trans _ _ _ s1 s2) s3) c))

(def-fns _ $ (many heap-spot : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (Spot) p))
  (let ((erased _) (many b) (erased lt)) (hread _ hp a))
  (let-match many b (BTag _ _ fs) (else (PosSpot $ NoPos)))
  (let ((erased _) (erased pw)) (refs-widen _ _ _ lt fs))
  (let-match many (coerce fs pw) (Cons _ f r1) ((Nil _) (PosSpot $ NoPos)))
  (let-match many r1 (Cons _ l r2) ((Nil _) (PosSpot $ NoPos)))
  (let-match many r2 (Cons _ c _) ((Nil _) (PosSpot $ NoPos)))
  (PosSpot $ MkPos (heap-str _ hp f) (heap-nat _ hp l) (heap-nat _ hp c)))

(def-fns _
  ((many syn-absolute : (many (String) file) (subterm many (Syn) r) -> (many (Syn) r2))
    (let ((many (Spot) p)) $ match many (raw-pos r) _ ((MkSpot l c) (PosSpot $ MkPos file l c)) (else (raw-pos r)))
    (match many r _
      ((RAtom _ s) (RAtom p s)) ((RWild _) (RWild p)) ((RNat _ n) (RNat p n)) ((RChr _ n) (RChr p n)) ((RString _ s) (RString p s))
      ((RList _ xs) (RList p $ notail $ syns-absolute file xs))))
  ((many syns-absolute : (many (String) file) (subterm many (List $ Syn) xs) -> (many (List $ Syn) r))
    (match many xs _ ((Nil _) (Nil _)) ((Cons _ x rest) (Cons _ (notail $ syn-absolute file x) $ notail $ syns-absolute file rest)))))

(def-fns _ $ (many heap-syns : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Maybe $ String) file) (subterm many (List $ Ref Block hs) refs) -> (many (String) f) (many (List $ Syn) xs))
  (let-match many refs (Cons _ a rest) ((Nil _) (values (match many file _ ((Some _ f) f) ((None _) "")) $ Nil _)))
  (let ((erased _) (many b) (erased _)) (hread _ hp a))
  (let-match many b (BExt _ p) (else (tail $ heap-syns _ hp file rest)))
  (let-match many p (PRaw g r) (else (tail $ heap-syns _ hp file rest)))
  (let ((many (Maybe $ String) adopted)) $ match many file _ ((Some _ f) (Some _ f)) ((None _) (match many (str-is-empty g) _ ((BTrue) (None _)) ((BFalse) (Some _ g)))))
  (let ((many f) (many xs)) $ notail $ heap-syns _ hp adopted rest)
  (values f $ Cons _ (match many (or (str-is-empty g) $ str-eqb f g) _ ((BTrue) r) ((BFalse) (syn-absolute g r))) xs))

(def-fns _ $ (many heap-handle : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (Name) n))
  (let ((erased _) (many b) (erased _)) (hread _ hp a))
  (let-match many b (BExt _ p) (else (NSrc "")))
  (match many p _ ((PHandle i rd m t) (NHandle i rd m t)) (else (NSrc ""))))

(def-fns _ $ (many heap-symbol : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (Name) n))
  (let ((erased _) (many b) (erased lt)) (hread _ hp a))
  (let-match many b (BTag _ _ fs) (else (NSrc "")))
  (let ((erased _) (erased pw)) (refs-widen _ _ _ lt fs))
  (let-match many (coerce fs pw) (Cons _ f r1) ((Nil _) (NSrc "")))
  (let-match many r1 (Cons _ s _) ((Nil _) (NSrc $ heap-str _ hp f)))
  (NGen (heap-nat _ hp f) $ heap-str _ hp s))

(def-fns _ $ (many raw-construct : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Nat) index) (many (List $ Ref Block hs) fields) -> (many (Payload) p))
  (let-match many fields (Cons _ pa more) ((Nil _) (PRaw "" $ RWild $ PosSpot $ NoPos)))
  (let ((many p)) $ heap-spot _ hp pa)
  (let ((many x)) $ match many more (((Ref Block hs) _)) ((Cons _ x _) x) ((Nil _) pa))
  (let-match many index (Succ i1) ((Zero) (PRaw "" $ RAtom p $ heap-symbol _ hp x)))
  (let-match many i1 (Succ i2) ((Zero) (PRaw "" $ RWild p)))
  (let-match many i2 (Zero) ((Succ _) (PRaw "" $ RAtom p $ heap-handle _ hp x)))
  (let-match many (list-refs (hsize _ hp) _ hp x) (Some _ refs) ((None _) (PRaw "" $ RList p $ Nil _)))
  (let ((many f) (many xs)) $ heap-syns _ hp (None _) refs)
  (PRaw f $ RList p xs))

(def-fns _ $ (many slots-block : (erased (Hist Block) hs) (subterm many (List $ Ref Block hs) ks) (many (Nat) n) (many (IdMap $ Ref Block hs) keys) (many (IdMap $ Nat) ids) -> (many (Block $ Ref Block hs) b))
  (let-match many ks (Cons _ k rest) ((Nil _) (BSlots _ n keys ids)))
  (tail $ slots-block _ rest (Succ n) (idmap-set _ n k keys) (idmap-set _ (ref-pos _ _ k) n ids)))

(def-fns _ $ (many slots-construct : (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ref Block hs) fields) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a))
  (let-match many fields (Cons _ l _) ((Nil _) (halloc _ hp (BError _ "slots constructor arity"))))
  (match many (list-refs (hsize _ hp) _ hp l) _
    ((None _) (halloc _ hp (BError _ "slots constructor: out of fuel")))
    ((Some _ ks) (halloc _ hp (slots-block _ (list-rev _ ks) 0 (MEmpty _) (MEmpty _))))))

(def-fns _ $ (many list-block : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ctor) nil) (many (Ctor) cons) (subterm many (List $ Ref Block hs) xs) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) a))
  (let-match many xs (Cons _ x rest) ((Nil _) (halloc _ hp $ BTag _ nil $ Nil _)))
  (let ((erased _) (many hp1) (erased s1) (many tl)) $ notail $ list-block _ hp nil cons rest)
  (let ((erased _) (erased pw)) (ref-widen _ _ _ s1 x))
  (let ((erased h2) (many hp2) (erased s2) (many c)) $ halloc _ hp1 $ BTag _ cons $ Cons _ (coerce x pw) $ Cons _ tl $ Nil _)
  (values h2 hp2 (hist-le-trans _ _ _ s1 s2) c))

(def-fns _ $ (many ext-construct : (erased (Hist Block) hs) (many (Heap hs) hp) (many (ExtType) ext) (many (Nat) index) (many (List $ Ref Block hs) fields) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a))
  (let-match many ext (ExtHalf)
    ((ExtArray) (array-construct _ hp index fields))
    ((ExtNat)
      (alloc-ext _ hp (PNat (match many index (((Nat) _))
        ((Zero) (Zero)) ((Succ _) (Succ (field-nat _ hp fields 0)))))))
    ((ExtString) (match many (cons-string _ hp index fields) _ ((Some _ s) (alloc-ext _ hp $ PStr s)) ((None _) (halloc _ hp $ BError _ "SCons: a code above 255"))))
    ((ExtBytes) (match many (cons-string _ hp index fields) _ ((Some _ s) (alloc-ext _ hp $ PBytes s)) ((None _) (halloc _ hp $ BError _ "BCons: a code above 255"))))
    ((ExtRaw _ _ _ _ _ _) (alloc-ext _ hp $ raw-construct _ hp index fields))
    ((ExtSlots _ _) (slots-construct _ hp fields)))
  (let ((many d) (erased _)) (double (field-nat _ hp fields 0)))
  (alloc-ext _ hp (PHalf (match many index (((Nat) _))
    ((Zero) 0) ((Succ k) (match many k (((Nat) _)) ((Zero) (Succ d)) ((Succ _) (Succ (Succ d)))))))))

(def-fns _ $ (many cons-destruct : (erased (Hist Block) hs) (many (Heap hs) hp) (many (String) s) (many (Bool) bytes) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Nat) index) (many (List $ Ref Block hs2) fields))
  (let-match many s (SCons c rest) ((SNil) (values hs hp (le-refl hs) 0 $ Nil _)))
  (let ((erased _) (many hp2) (erased sf2) (many a1)) $ alloc-ext _ hp $ PNat $ char-code c)
  (let ((erased hl3) (many hp3) (erased sf3) (many a2)) $ alloc-ext _ hp2 $ match many bytes (((Payload) _)) ((BTrue) (PBytes rest)) ((BFalse) (PStr rest)))
  (let ((erased _) (erased p1)) (ref-widen _ _ _ sf3 a1))
  (values hl3 hp3 (hist-le-trans _ _ _ sf2 sf3) 1 $ Cons _ (coerce a1 p1) $ Cons _ a2 $ Nil _))

(def-fns _ $ (many symbol-block : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ctor) sname) (many (Ctor) sgen) (many (Name) n) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) a))
  (let ((many (Ctor) c) (many (List $ Payload) ps)) $ match many n (((Ctor) _) ((List $ Payload) _))
    ((NGen k t) (values sgen $ Cons _ (PNat k) $ Cons _ (PStr t) $ Nil _))
    (else (values sname $ Cons _ (PStr $ name-text n) $ Nil _)))
  (let ((erased _) (many hp1) (erased s1) (many rs)) $ alloc-payloads _ hp ps)
  (let ((erased h2) (many hp2) (erased s2) (many a)) $ halloc _ hp1 $ BTag _ c rs)
  (values h2 hp2 (hist-le-trans _ _ _ s1 s2) a))

(def-fns _ $ (many raw-second : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ctor) nl) (many (Ctor) cs) (many (Ctor) sn) (many (Ctor) sg) (many (String) f) (many (Syn) r) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Nat) index) (many (Ref Block hs2) a))
  (match many r _
    ((RList _ xs) (let ((erased h2) (many hp2) (erased s2) (many a)) $ raw-list _ hp nl cs f xs) (values h2 hp2 s2 2 a))
    ((RAtom _ nm)
      (match many nm _
        ((NHandle x rd m t) (let ((erased h2) (many hp2) (erased s2) (many a)) $ alloc-ext _ hp $ PHandle x rd m t) (values h2 hp2 s2 3 a))
        (else (let ((erased h2) (many hp2) (erased s2) (many a)) $ symbol-block _ hp sn sg nm) (values h2 hp2 s2 0 a))))
    (else (let ((erased h2) (many hp2) (erased s2) (many a)) $ halloc _ hp $ BError _ "a literal is a handle in a macro's arguments") (values h2 hp2 s2 3 a))))

(def-fns _ $ (many raw-destruct : (erased (Hist Block) hs) (many (Heap hs) hp) (many (ExtType) e) (many (String) f) (many (Syn) r) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Nat) index) (many (List $ Ref Block hs2) fields))
  (let-match many e (ExtRaw np mp nl cs sn sg) (else (values hs hp (le-refl hs) 0 $ Nil _)))
  (let ((erased h1) (many hp1) (erased s1) (many pv)) $ pos-block _ hp np mp f $ raw-pos r)
  (let-match many r (RWild _) (else
    (let ((erased h2) (many hp2) (erased s2) (many i) (many a)) $ raw-second _ hp1 nl cs sn sg f r)
    (let ((erased _) (erased pw)) (ref-widen _ _ _ s2 pv))
    (values h2 hp2 (hist-le-trans _ _ _ s1 s2) i $ Cons _ (coerce pv pw) $ Cons _ a $ Nil _)))
  (values h1 hp1 s1 1 $ Cons _ pv $ Nil _))

(def-fns _ $ (many ext-destruct : (erased (Hist Block) hs) (many (Heap hs) hp) (many (ExtType) e) (many (Payload) p) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Nat) index) (many (List $ Ref Block hs2) fields))
  (match many p _
    ((PRaw f r) (tail $ raw-destruct _ hp e f r))
    ((PNat n)
      (let-match many n (Succ k) ((Zero) (values hs hp (le-refl hs) 0 $ Nil _)))
      (let ((erased hl2) (many hp2) (erased sf2) (many a)) $ alloc-ext _ hp $ PNat k)
      (values hl2 hp2 sf2 1 $ Cons _ a $ Nil _))
    ((PHalf n)
      (match many (nat-halve n) _
        ((HZ) (values hs hp (le-refl hs) 0 $ Nil _))
        ((H1 m _ _)
          (let ((erased hl2) (many hp2) (erased sf2) (many a)) $ alloc-ext _ hp $ PNat m)
          (values hl2 hp2 sf2 1 $ Cons _ a $ Nil _))
        ((H2 m _ _)
          (let ((erased hl2) (many hp2) (erased sf2) (many a)) $ alloc-ext _ hp $ PNat m)
          (values hl2 hp2 sf2 2 $ Cons _ a $ Nil _))))
    ((PStr s) (tail $ cons-destruct _ hp s (BFalse)))
    ((PBytes s) (tail $ cons-destruct _ hp s (BTrue)))
    ((PHandle _ _ _ _) (values hs hp (le-refl hs) 0 $ Nil _))))


(def-fns _ $ (many tuple : (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ref Block hs) vs) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many vs _
    ((Nil _)
      (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ halloc _ hp $ BToken _)
      (values hl2 hp2 sf2 v))
    ((Cons _ v rest)
      (let-match many rest (Cons _ _ _) ((Nil _) (values hs hp (le-refl hs) v)))
      (let ((erased hl2) (many hp2) (erased sf2) (many t)) $ halloc _ hp $ BTup _ vs)
      (values hl2 hp2 sf2 t))))

(def-fns _ $ (many untuple : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Nat) n) (many (Ref Block hs) v) -> (many (List $ Ref Block hs) vs))
  (let-match many n (Succ k) ((Zero) (Nil _)))
  (let-match many k (Succ _) ((Zero) (Cons _ v $ Nil _)))
  (let ((erased _) (many b) (erased lt)) (hread _ hp v))
  (let-match many b (BTup _ fs) (else (Nil $ Ref Block hs)))
  (let ((erased _) (erased p2)) (refs-widen _ _ _ lt fs))
  (coerce fs p2))

(def-fns _ $ (many ctor-fields : (erased (Hist Block) hs) (many (Heap hs) hp)
    (many (Bool) is-newtype) (many (Nat) arity) (many (Ref Block hs) v) -> (many (List $ Ref Block hs) fields))
  (let-match many is-newtype (BFalse) ((BTrue) (untuple _ hp arity v)))
  (let ((erased _) (many body) (erased sf)) (hread _ hp v))
  (let-match many body (BTag _ _ fs) (else (Nil _)))
  (let ((erased _) (erased pf)) (refs-widen _ _ _ sf fs))
  (coerce fs pf))

(def-fns _ $ (many settled-ref : (erased (Hist Block) hs) (many (IdMap $ EInfo hs) en) (many (Nat) x) -> (many (Maybe $ Ref Block hs) r))
  (let-match many (idmap-get _ x en) (Hit _ _ _ info _) ((Miss _ _ _ _) (None _)))
  (let-match many info (MkEInfo _ _ _ s _ _ _ _))
  (match many s _ ((SHypothetical _) (None _)) ((SSettled _ v _) (Some _ v))))

(def-fns _ $ (many hollow-shape : (many (Bool) tagged) (many (List $ Nat) arities) -> (many (Bool) r))
  (and (not tagged) $ nat-list-eq arities $ list-replicate _ (list-length _ arities) 0))

(def-fns _ $ (many construct : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ctor) c) (many (List $ Ref Block hs) args) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many c (MkCtor _ _ index _ tagged ext shape newtype2))
  (match many ext _
    ((Some _ e)
      (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ ext-construct _ hp e index args)
      (values hl2 hp2 sf2 v))
    ((None _)
      (let-match many newtype2 (BFalse) ((BTrue) (tuple _ hp args)))
      (let ((many vacant)) $ match many (hollow-shape tagged shape) (((Maybe $ Ref Block hs) _)) ((BTrue) (settled-ref _ (heap-entries _ hp) null-id)) ((BFalse) (None _)))
      (let-match many vacant (None _) ((Some _ v) (values hs hp (le-refl hs) v)))
      (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ halloc _ hp $ BTag _ c args)
      (values hl2 hp2 sf2 v))))

; A value's discriminant and many fields where the FFI holds the type or a tag says (section 33); None
; otherwise, the value then being its fields as they stand.
(def-fns _ $ (many dispatch : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Maybe $ ExtType) ext) (many (Bool) tagged) (many (List $ Nat) shape) (many (Ref Block hs) v) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Maybe $ Pair (Nat) $ List $ Ref Block hs2) r))
  (let ((erased _) (many b) (erased lt)) (hread _ hp v))
  (let ((many as-word)) $ word-of-block _ b)
  (let-match many as-word (None _)
    ((Some _ w)
      (match many ext _
        ((Some _ e)
          (let ((erased hs2) (many hp2) (erased le) (many i) (many fs)) $ ext-destruct _ hp e $ PNat w)
          (values hs2 hp2 le $ Some _ $ MkPair _ _ i fs))
        ((None _)
          (match many tagged _
            ((BTrue) (values hs hp (le-refl hs) $ Some _ $ MkPair _ _ (fieldless-index shape w) $ Nil _))
            ((BFalse) (values hs hp (le-refl hs) $ None _)))))))
  (match many b _
    ((BExt _ p)
      (let-match many ext (Some _ e) ((None _) (values hs hp (le-refl hs) $ None _)))
      (let ((erased hs2) (many hp2) (erased le) (many i) (many fs)) $ ext-destruct _ hp e p)
      (values hs2 hp2 le $ Some _ $ MkPair _ _ i fs))
    ((BArray _ _ _)
      (let-match many ext (Some _ e) ((None _) (values hs hp (le-refl hs) (None _))))
      (let-match many e (ExtArray) (else (values hs hp (le-refl hs) (None _))))
      (let ((erased h2) (many hp2) (erased le2) (many i) (many fields)) (array-destruct _ hp v))
      (values h2 hp2 le2 (Some _ (MkPair _ _ i fields))))
    ((BSlots _ n ks _)
      (let-match many ext (Some _ e) ((None _) (values hs hp (le-refl hs) (None _))))
      (let-match many e (ExtSlots nl cs) (else (values hs hp (le-refl hs) (None _))))
      (let ((erased _) (erased pw)) (idmap-widen _ _ _ lt ks))
      (let ((erased h2) (many hp2) (erased le2) (many l)) (list-block _ hp nl cs (list-rev _ $ idmap-prefix _ (coerce ks pw) n $ Nil _)))
      (values h2 hp2 le2 (Some _ (MkPair _ _ 0 (Cons _ l (Nil _))))))
    ((BTag _ ct fs)
      (let-match many tagged (BTrue) ((BFalse) (values hs hp (le-refl hs) $ None _)))
      (let ((erased _) (erased p3)) (refs-widen _ _ _ lt fs))
      (values hs hp (le-refl hs) $ Some _ $ MkPair _ _ (ctor-index ct) (coerce fs p3)))
    (else (values hs hp (le-refl hs) $ None _))))

(def-fns _ $ (many destruct : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ctor) c) (many (Ref Block hs) v) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Maybe $ Nat) i) (many (List $ Ref Block hs2) fields))
  (let-match many c (MkCtor _ _ index arity tagged ext shape newtype2))
  (let ((erased hs2) (many hp2) (erased le) (many read)) $ dispatch _ hp ext tagged shape v)
  (let-match many read (None _) ((Some _ p) (match many p _ ((MkPair _ _ i fs) (values hs2 hp2 le (Some _ i) fs)))))
  (let ((erased _) (erased p4)) (ref-widen _ _ _ le v))
  (let ((many sole)) $ and (not $ is-some _ ext) $ and (not tagged) $ nat-eqb 1 $ list-length _ shape)
  (values hs2 hp2 le (match many sole (((Maybe $ Nat) _)) ((BTrue) (Some _ index)) ((BFalse) (None _))) $ ctor-fields _ hp2 newtype2 arity (coerce v p4)))

(def-fns _ $ (many headed-by : (many (Maybe $ Nat) i) (many (Ctor) c) -> (many (Bool) r))
  (match many i _ ((Some _ j) (nat-eqb j $ ctor-index c)) ((None _) (BFalse))))

(def-fns _ $ (many ctor-at : (many (Adt) adt) (many (Nat) i) -> (many (Maybe $ Ctor) c))
  (match many (list-nth _ (adt-ctors adt) i) _ ((NthHit _ _ _ c _) (Some _ c)) ((NthMiss _ _ _ _) (None _))))

(def-fns _ $ (many vnat : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Nat) n) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) sf) (many (Ref Block hs2) a))
  (alloc-ext _ hp $ PNat n))

(def-fns _ $ (many rope-of-payload : (many (Payload) pp) -> (many (Result $ Rope) r))
  (let-match many pp (PNat m) ((PStr str) (Ok _ $ RStr str)) (else (Ok _ $ REmpty)))
  (match many (char-of-nat m) _ ((Some _ c) (Ok _ $ RChar c)) ((None _) (Fail _ "flatten: a code above 255"))))

(def-fns _
  ((many rope-walk : (subterm many (Nat) fuel) (erased (Hist Block) hs)
      (many (Heap hs) hp) (many (Ref Block hs) r) -> (many (Result $ Rope) rope))
    (let-match many fuel (Succ k) ((Zero) (Fail _ "flatten: out of fuel")))
    (let ((erased _) (many body) (erased sf)) (hread _ hp r))
    (let-match many body (BTag _ _ fields)
      ((BExt _ pp) (rope-of-payload pp))
      (else (Ok _ $ REmpty)))
    (let ((erased _) (erased pf)) (refs-widen _ _ _ sf fields))
    (tail $ rope-fields k _ hp (coerce fields pf)))
  ((many rope-fields : (subterm many (Nat) fuel) (erased (Hist Block) hs)
      (many (Heap hs) hp) (subterm many (List $ Ref Block hs) fs) -> (many (Result $ Rope) rope))
    (let-match many fs (Cons _ f rest) ((Nil _) (Ok _ $ REmpty)))
    (let-match many fuel (Succ k) ((Zero) (Fail _ "flatten: out of fuel")))
    (let-match many (notail $ rope-walk k _ hp f) (Ok _ a) ((Fail _ m) (Fail _ m)))
    (let-match many (notail $ rope-fields fuel _ hp rest) (Ok _ b) ((Fail _ m) (Fail _ m)))
    (Ok _ $ RCat a b)))

(def-fns _ $ (many flatten-value : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) r) -> (many (Result $ String) s))
  (let-match many (rope-walk (nat-mul 2 $ hsize _ hp) _ hp r) (Ok _ rope) ((Fail _ m) (Fail _ m)))
  (let ((many str) (erased _)) $ flatten rope)
  (Ok _ str))

(def-fns _ $ (many alloc-one : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Block $ Ref Block hs) body) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r))
  (let ((erased h2) (many hp2) (erased le2) (many v)) (halloc _ hp body))
  (values h2 hp2 le2 (Cons _ v (Nil _))))

; What an extern's implementation produces: a payload, a pair of them, or the constructor of a plain type at
; its discriminant. The dispatch below has one case per Extern and no else, so a new one has to say which.
(def-adts $ (ExtResult : -> Type)
  enum
  (many ErPayload : (many (Payload) p) -> (ExtResult))
  (many ErPair : (many (Payload) a) (many (Payload) b) -> (ExtResult))
  (many ErCtor : (many (Nat) index) (many (List $ Payload) fields) -> (ExtResult))
  (many ErError : (many (String) message) -> (ExtResult))
  (many ErArrayNew : (many (Nat) count) -> (ExtResult))
  (many ErArraySwap : -> (ExtResult))
  (many ErArrayPluck : -> (ExtResult))
  (many ErArrayPlace : -> (ExtResult))
  (many ErListToArray : -> (ExtResult))
  (many ErArrayMake : (many (Nat) count) -> (ExtResult))
  (many ErWrite : (many (Nat) arg) (many (Payload) p) -> (ExtResult))
  (many ErArrayCopy : -> (ExtResult))
  (many ErArraySub : (many (Nat) i) (many (Nat) n) -> (ExtResult))
  (many ErArrayBlit : (many (Nat) i) (many (Nat) j) (many (Nat) n) -> (ExtResult))
  (many ErSlotsNew : -> (ExtResult))
  (many ErSlotsLookup : (many (Bool) adding) -> (ExtResult)))

; An extern function over its arguments (section 42). The arguments are counted against the arity here, the
; call having been checked against the model's telescope; [cs] are the constructors of the plain type it
; builds, read off that model's return type at the extern mark.
(def-fns _ $ (many array-writes : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) dst) (many (Nat) j) (subterm many (List $ Ref Block hs) vs) -> (many (Heap hs) hp2))
  (let-match many vs (Cons _ v rest) ((Nil _) hp))
  (let ((many hp1) (many _)) (array-change _ hp dst j $ Some _ v))
  (tail $ array-writes _ hp1 dst (Succ j) rest))

(def-fns _ $ (many apply-array-change : (erased (Hist Block) hs) (many (Heap hs) hp)
    (many (Maybe $ Ref Block hs) array) (many (Nat) index) (many (Maybe $ Ref Block hs) replacement)
    (many (Bool) return-old) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2)
    (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r))
  (let ((many (Heap hs) hp1) (many (Maybe $ Ref Block hs) old))
    (match many array _
      ((None _) (values hp (None _)))
      ((Some _ a) (array-change _ hp a index replacement))))
  (let-match many old (None _)
    ((Some _ v)
      (values hs hp1 (le-refl hs) (match many return-old (((List $ Ref Block hs) _)) ((BTrue) (Cons _ v (Nil _))) ((BFalse) (Nil _))))))
  (let ((erased h2) (many hp2) (erased le2) (many err)) (halloc _ hp1 (BError _ "invalid array access")))
  (values h2 hp2 le2 (Cons _ err (Nil _))))

(def-fns _ $ (many result-ctor : (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ctor) cs) (many (Nat) i) (many (List $ Payload) ps) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r))
  (let-match many (list-nth _ cs i) (NthHit _ _ _ c _)
    ((NthMiss _ _ _ _) (alloc-one _ hp $ BError _ "the extern implementation has no constructor to build its result with")))
  (let ((erased _) (many hp1) (erased s1) (many rs)) $ alloc-payloads _ hp ps)
  (let ((erased h2) (many hp2) (erased s2) (many v)) $ construct _ hp1 c rs)
  (values h2 hp2 (hist-le-trans _ _ _ s1 s2) $ Cons _ v $ Nil _))

(def-fns _ $ (many slots-count : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) t) -> (many (Nat) n))
  (let ((erased _) (many body) (erased _)) (hread _ hp t))
  (match many body _ ((BSlots _ n _ _) n) (else 0)))

(def-fns _ $ (many slots-lookup : (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ctor) cs) (many (Ref Block hs) t) (many (Ref Block hs) k) (many (Bool) adding) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r))
  (let ((erased _) (many body) (erased lt)) (hread _ hp t))
  (let-match many body (BSlots _ n ks ids) (else (alloc-one _ hp $ BError _ "not a slot table")))
  (let-match many (idmap-get _ (ref-pos _ _ k) ids) (Miss _ _ _ _) ((Hit _ _ _ i _) (result-ctor _ hp cs 0 $ Cons _ (PNat i) $ Nil _)))
  (let-match many adding (BTrue) ((BFalse) (result-ctor _ hp cs 1 $ Nil _)))
  (let ((erased _) (erased pw)) (idmap-widen _ _ _ lt ks))
  (let ((many hp1)) (hwrite _ hp t $ BSlots _ (Succ n) (idmap-set _ n k $ coerce ks pw) (idmap-set _ (ref-pos _ _ k) n ids)))
  (result-ctor _ hp1 cs 1 $ Cons _ (PNat n) $ Nil _))

(def-fns _ $ (many apply-extern : (erased (Nat) n) (many (Extern n) e) (many (List $ Ctor) cs) (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ref Block hs) args) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r))
  (let ((many (Maybe $ Ref Block hs) a)) $ match many (list-nth _ args 0) _ ((NthHit _ _ _ x _) (Some _ x)) ((NthMiss _ _ _ _) (None _)))
  (let ((many (Maybe $ Ref Block hs) b)) $ match many (list-nth _ args 1) _ ((NthHit _ _ _ x _) (Some _ x)) ((NthMiss _ _ _ _) (None _)))
  (let ((many (Nat) na)) $ match many a _ ((Some _ x) (heap-nat _ hp x)) ((None _) 0))
  (let ((many (Nat) nb)) $ match many b _ ((Some _ x) (heap-nat _ hp x)) ((None _) 0))
  (let ((many (String) sa)) $ match many a _ ((Some _ x) (heap-str _ hp x)) ((None _) (SNil)))
  (let ((many (String) sb)) $ match many b _ ((Some _ x) (heap-str _ hp x)) ((None _) (SNil)))
  (let ((many (ExtResult) res))
    (match many (ext-twin _ e) _
      ((ExArrayNew) (ErArrayNew na))
      ((ExArraySwap) (ErArraySwap))
      ((ExArrayPluck) (ErArrayPluck))
      ((ExArrayPlace) (ErArrayPlace))
      ((ExArrayLength)
        (ErPayload $ PNat $ match many (match many a (((Maybe $ Pair (Nat) $ IdMap $ Ref Block hs) _)) ((Some _ x) (array-elems _ hp x)) ((None _) (None _))) (((Nat) _))
          ((Some _ ne) (match many ne _ ((MkPair _ _ len _) len))) ((None _) 0)))
      ((ExArrayLengthDec) (ErCtor 0 $ Nil _))
      ((ExBytesLengthDec) (ErCtor 0 $ Nil _))
      ((ExListToArray) (ErListToArray))
      ((ExBytesMake)
        (let-match many (char-of-nat nb) (Some _ c) ((None _) (ErError "bytes-make: a code above 255")))
        (let ((many s) (erased _)) (flatten $ byte-run na c))
        (ErPayload $ PBytes s))
      ((ExBytesGet) (match many (byte-at sa nb) _ ((Some _ k) (ErPayload $ PNat k)) ((None _) (ErError "bytes-get: past the end"))))
      ((ExBytesSet)
        (let-match many (char-of-nat $ field-nat _ hp args 2) (Some _ c) ((None _) (ErError "bytes-set: a code above 255")))
        (ErWrite 0 $ PBytes $ str-splice sa nb 1 $ RChar c))
      ((ExBytesSub) (let ((many s) (erased _)) (flatten $ str-range sa nb (field-nat _ hp args 2) $ REmpty)) (ErPayload $ PBytes s))
      ((ExBytesBlit)
        (let ((many count)) (field-nat _ hp args 4))
        (let ((many (String) dst)) $ match many (list-nth _ args 2) _ ((NthHit _ _ _ x _) (heap-str _ hp x)) ((NthMiss _ _ _ _) (SNil)))
        (ErWrite 2 $ PBytes $ str-splice dst (field-nat _ hp args 3) count $ str-range sa nb count $ REmpty))
      ((ExArraySub) (ErArraySub nb $ field-nat _ hp args 2))
      ((ExArrayBlit) (ErArrayBlit nb (field-nat _ hp args 3) (field-nat _ hp args 4)))
      ((ExBytesLength) (let ((many len) (erased _)) (str-length sa)) (ErPayload $ PNat len))
      ((ExStrBytesCopy) (ErPayload $ PBytes sa))
      ((ExBytesCopy) (ErPayload $ PBytes sa))
      ((ExArrayCopy) (ErArrayCopy))
      ((ExBytesStr) (ErPayload $ PStr sa))
      ((ExArrayMake) (ErArrayMake na))
      ((ExSlotsNew) (ErSlotsNew))
      ((ExSlotsFind) (ErSlotsLookup $ BFalse))
      ((ExSlotsIntern) (ErSlotsLookup $ BTrue))
      ((ExSlotsLength) (ErPayload $ PNat $ match many a (((Nat) _)) ((Some _ x) (slots-count _ hp x)) ((None _) 0)))
      ((ExAdd) (ErPayload $ PNat $ nat-add na nb))
      ((ExSub)
        (let-match many (lt-dec nb (Succ na)) (Yes _ _ _ _ le)
          ((No _ _ _ _ _) (ErError "sub: negative result")))
        (let ((many c) (erased _)) $ sub na nb le)
        (ErPayload $ PNat c))
      ((ExMul) (ErPayload $ PNat $ nat-mul na nb))
      ((ExShl) (ErPayload $ PNat $ nat-shl na nb))
      ((ExShr) (ErPayload $ PNat $ nat-shr na nb))
      ((ExU62Inc) (ErPayload $ PNat $ Succ na))
      ((ExU62Dec) (ErPayload $ PNat $ match many na (((Nat) _)) ((Zero) (Zero)) ((Succ m) m)))
      ((ExNatAnd) (let ((many c) (erased _)) $ nat-and na nb) (ErPayload $ PNat c))
      ((ExNatOr) (let ((many c) (erased _)) $ nat-or na nb) (ErPayload $ PNat c))
      ((ExNatXor) (let ((many c) (erased _)) $ nat-xor na nb) (ErPayload $ PNat c))
      ((ExDiv)
        (let-match many (lt-dec (Zero) nb) (Yes _ _ _ _ pos)
          ((No _ _ _ _ _) (ErError "div: zero divisor")))
        (let ((many d) (erased _) (erased _) (erased _) (erased _) (erased _)) $ div na nb pos)
        (ErPayload $ PNat d))
      ((ExNatCmp) (ErCtor (cmp-index _ _ _ _ $ nat-cmp na nb) $ Nil _))
      ((ExLtDec) (ErCtor (match many (lt-dec na nb) (((Nat) _)) ((Yes _ _ _ _ _) 0) ((No _ _ _ _ _) 1)) $ Nil _))
      ((ExStrCmp) (ErCtor (cmp-index _ _ _ _ $ str-cmp sa sb) $ Nil _))
      ((ExNatEq) (ErCtor (match many (nat-eq na nb) (((Nat) _)) ((Equal _ _ _) 0) ((Unequal _ _ _ _ _) 1)) $ Nil _))
      ((ExStrEq) (ErCtor (match many (str-eq sa sb) (((Nat) _)) ((Equal _ _ _) 0) ((Unequal _ _ _ _ _) 1)) $ Nil _))
      ((ExBitLength) (ErPayload $ PNat $ nat-bit-length na))
      ((ExBitTest) (ErCtor (match many (nat-bit-test na nb) (((Nat) _)) ((Bit0) 0) ((Bit1) 1)) $ Nil _))
      ((ExNatHalve) (ErPayload $ PHalf na))
      ((ExStrLength) (let ((many len) (erased _)) (str-length sa)) (ErPayload $ PNat len))
      ((ExStrGet) (match many (byte-at sa nb) _ ((Some _ k) (ErPayload $ PNat k)) ((None _) (ErError "str-get: past the end"))))
      ((ExNatStr) (ErPayload $ PStr $ nat-str na))
      ((ExStrNat) (match many (str-nat sa) _ ((None _) (ErCtor 0 $ Nil _)) ((Some _ k) (ErCtor 1 $ Cons _ (PNat k) $ Nil _))))
      ((ExNatMod)
        (let-match many (lt-dec (Zero) nb) (Yes _ _ _ _ pos)
          ((No _ _ _ _ _) (ErError "nat-mod: zero modulus")))
        (let ((many m) (erased _) (erased _)) $ nat-mod na nb pos)
        (ErPayload $ PNat m))
      ((ExTrim) (ErPayload $ PStr $ trim sa))
      ((ExAppend) (ErPayload $ PStr $ str-append sa sb))
      ((ExFlatten)
        (let-match many a (Some _ x) ((None _) (ErPayload $ PStr $ SNil)))
        (match many (flatten-value _ hp x) _ ((Ok _ str) (ErPayload $ PStr str)) ((Fail _ m) (ErError m))))
      ((ExStrSplit)
        (let ((many len) (erased l)) $ str-length sa)
        (let-match many (lt-dec nb (Succ len)) (Yes _ _ _ _ le) ((No _ _ _ _ _) (ErError "str-split: past the end")))
        (let ((many a1) (many b1) (erased _) (erased _)) $ str-split sa nb len l le)
        (ErPair (PStr a1) (PStr b1)))
      ((ExDivmod)
        (let-match many (lt-dec (Zero) nb) (Yes _ _ _ _ pos) ((No _ _ _ _ _) (ErError "divmod: zero divisor")))
        (let ((many quo) (many rem) (erased _) (erased _) (erased _) (erased _)) $ divmod na nb pos)
        (ErPair (PNat quo) (PNat rem)))
      (else (ErPayload $ PStr "an extern with no implementation of its own"))))
  (match many res _
    ((ErArrayNew length2)
      (let-match many (settled-ref _ (heap-entries _ hp) null-id) (Some _ blank) ((None _) (alloc-one _ hp (BError _ "array-new: no vacant-slot"))))
      (alloc-one _ hp (array-block _ (repeat-field _ length2 blank))))
    ((ErListToArray)
      (alloc-one _ hp $ match many (match many a (((Maybe $ List $ Ref Block hs) _)) ((Some _ x) (list-refs (hsize _ hp) _ hp x)) ((None _) (Some _ $ Nil _))) _
        ((Some _ xs) (array-block _ xs)) ((None _) (BError _ "list-to-array: out of fuel"))))
    ((ErArrayMake length2)
      (alloc-one _ hp (array-block _ (match many b (((List $ Ref Block hs) _)) ((Some _ x) (repeat-field _ length2 x)) ((None _) (Nil _))))))
    ((ErArrayPluck) (apply-array-change _ hp a nb (None _) (BTrue)))
    ((ErArraySwap)
      (let ((many replacement)) (match many (list-nth _ args 2) (((Maybe $ Ref Block hs) _))
        ((NthHit _ _ _ x _) (Some _ x)) ((NthMiss _ _ _ _) (None _))))
      (apply-array-change _ hp a nb replacement (BTrue)))
    ((ErArrayPlace)
      (let ((many replacement)) (match many (list-nth _ args 2) (((Maybe $ Ref Block hs) _))
        ((NthHit _ _ _ x _) (Some _ x)) ((NthMiss _ _ _ _) (None _))))
      (apply-array-change _ hp a nb replacement (BFalse)))
    ((ErArrayCopy)
      (alloc-one _ hp (array-block _ (match many a (((List $ Ref Block hs) _)) ((Some _ x) (match many (array-fields _ hp x) _ ((Some _ fs) fs) ((None _) (Nil _)))) ((None _) (Nil _))))))
    ((ErWrite k p)
      (values hs (match many (list-nth _ args k) _ ((NthHit _ _ _ x _) (hwrite _ hp x $ BExt _ p)) ((NthMiss _ _ _ _) hp)) (le-refl hs) (Nil _)))
    ((ErArraySub i count)
      (alloc-one _ hp (array-block _ (list-range _ (match many a (((List $ Ref Block hs) _)) ((Some _ x) (match many (array-fields _ hp x) _ ((Some _ fs) fs) ((None _) (Nil _)))) ((None _) (Nil _))) i count))))
    ((ErArrayBlit i j count)
      (let ((many (List $ Ref Block hs) vs)) (match many a _ ((Some _ x) (match many (array-fields _ hp x) _ ((Some _ fs) (list-range _ fs i count)) ((None _) (Nil _)))) ((None _) (Nil _))))
      (values hs (match many (list-nth _ args 2) _ ((NthHit _ _ _ d _) (array-writes _ hp d j vs)) ((NthMiss _ _ _ _) hp)) (le-refl hs) (Nil _)))
    ((ErPayload p) (alloc-one _ hp $ BExt _ p))
    ((ErError m) (alloc-one _ hp $ BError _ m))
    ((ErPair p q)
      (let ((erased _) (many hp2) (erased sf2) (many v1)) $ alloc-ext _ hp p)
      (let ((erased hl3) (many hp3) (erased sf3) (many v2)) $ alloc-ext _ hp2 q)
      (let ((erased _) (erased pw1)) (ref-widen _ _ _ sf3 v1))
      (values hl3 hp3 (hist-le-trans _ _ _ sf2 sf3) $ Cons _ (coerce v1 pw1) $ Cons _ v2 $ Nil _))
    ((ErCtor i ps) (result-ctor _ hp cs i ps))
    ((ErSlotsNew) (alloc-one _ hp $ BSlots _ 0 (MEmpty _) (MEmpty _)))
    ((ErSlotsLookup adding)
      (let-match many a (Some _ t) ((None _) (alloc-one _ hp $ BError _ "slots: no table")))
      (let-match many b (Some _ k) ((None _) (alloc-one _ hp $ BError _ "slots: no slot")))
      (slots-lookup _ hp cs t k adding))))

; ---- Values at every position of a code's index (ASSUMPTIONS 125): a code's values are the list of its
; many results, with a Picked reading them back against the index. Nothing converts between the two
; representations along a call, which is what lets a call in tail position compile to one (section 19).

(def-fns _ $ (many vals-of : (erased (Hist Block) hs) (subterm many (List $ Multiplicity) ms) (many (Ref Block hs) v) -> (many (List $ Ref Block hs) r) (erased (Picked (Ref Block hs) ms r) pk))
  (let-match many ms (Cons _ m rest) ((Nil _) (values (Nil _) (PkNil _))))
  (let ((many r) (erased pk)) $ notail $ vals-of _ rest v)
  (match many m _
    ((Many) (values (Cons _ v r) (PkMany _ rest v r pk)))
    ((Once) (values (Cons _ v r) (PkOnce _ rest v r pk)))
    ((Erased) (values r (PkErased _ rest r pk)))))

(def-fns _ $ (many error-vals : (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Multiplicity) ms) (many (String) msg) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (erased (Picked (Ref Block hs2) ms vs) pk))
  (let ((erased hl2) (many hp2) (erased sf2) (many e)) $ halloc _ hp $ BError _ msg)
  (let ((many vs) (erased pk)) $ vals-of _ ms e)
  (values hl2 hp2 sf2 vs pk))

; Cut or padded to the index, a closure's arity being a runtime property; a missing value is an error block.
(def-fns _ $ (many vals-fit : (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (List $ Multiplicity) ms) (many (List $ Ref Block hs) vs) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r) (erased (Picked (Ref Block hs2) ms r) pk))
  (let-match many ms (Cons _ m rest) ((Nil _) (values hs hp (le-refl hs) (Nil _) (PkNil _))))
  (match many m _
    ((Erased)
      (let ((erased hs2) (many hp2) (erased le) (many r) (erased pk)) $ tail $ vals-fit _ hp rest vs)
      (values hs2 hp2 le r (PkErased _ rest r pk)))
    ((Many)
      (match many vs _
        ((Nil _)
          (let ((erased _) (many hp2) (erased sf2) (many e)) $ halloc _ hp $ BError _ "arity mismatch")
          (let ((erased hs3) (many hp3) (erased le3) (many r) (erased pk)) $ notail $ vals-fit _ hp2 rest $ Nil _)
          (let ((erased _) (erased pe1)) (ref-widen _ _ _ le3 e))
          (let ((many e2)) (coerce e pe1))
          (values hs3 hp3 (hist-le-trans _ _ _ sf2 le3) (Cons _ e2 r) (PkMany _ rest e2 r pk)))
        ((Cons _ v vrest)
          (let ((erased hs2) (many hp2) (erased le) (many r) (erased pk)) $ notail $ vals-fit _ hp rest vrest)
          (let ((erased _) (erased pv1)) (ref-widen _ _ _ le v))
          (let ((many v2)) (coerce v pv1))
          (values hs2 hp2 le (Cons _ v2 r) (PkMany _ rest v2 r pk)))))
    ((Once)
      (match many vs _
        ((Nil _)
          (let ((erased _) (many hp2) (erased sf2) (many e)) $ halloc _ hp $ BError _ "arity mismatch")
          (let ((erased hs3) (many hp3) (erased le3) (many r) (erased pk)) $ notail $ vals-fit _ hp2 rest $ Nil _)
          (let ((erased _) (erased pe1)) (ref-widen _ _ _ le3 e))
          (let ((many e2)) (coerce e pe1))
          (values hs3 hp3 (hist-le-trans _ _ _ sf2 le3) (Cons _ e2 r) (PkOnce _ rest e2 r pk)))
        ((Cons _ v vrest)
          (let ((erased hs2) (many hp2) (erased le) (many r) (erased pk)) $ notail $ vals-fit _ hp rest vrest)
          (let ((erased _) (erased pv1)) (ref-widen _ _ _ le v))
          (let ((many v2)) (coerce v pv1))
          (values hs2 hp2 le (Cons _ v2 r) (PkOnce _ rest v2 r pk)))))))

; The one value of a size-one code: the Picked refutes an empty list.
(def-fns _ $ (many vals-one : (erased (Hist Block) hs) (many (List $ Ref Block hs) vs) (erased (Picked (Ref Block hs) many-one vs) pk) -> (many (Ref Block hs) v))
  (match many vs _
    ((Cons _ x _) x)
    (absurd (Nil _) pk)))

; A branch's fields or a closure's arguments bound to their ids, cut or padded to their count.
(def-fns _ $ (many fit-addrs : (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (List $ Nat) ids) (many (List $ Ref Block hs) vs) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) r) (erased (Lockstep (Nat) (Ref Block hs2) ids r) lk))
  (let-match many ids (Cons _ x rest) ((Nil _) (values hs hp (le-refl hs) (Nil _) (LsNil _ _))))
  (match many vs _
    ((Nil _)
      (let ((erased _) (many hp2) (erased sf2) (many e)) $ halloc _ hp $ BError _ "arity mismatch")
      (let ((erased hs3) (many hp3) (erased le3) (many r) (erased lk)) $ notail $ fit-addrs _ hp2 rest $ Nil _)
      (let ((erased _) (erased pe2)) (ref-widen _ _ _ le3 e))
      (let ((many e2)) (coerce e pe2))
      (values hs3 hp3 (hist-le-trans _ _ _ sf2 le3) (Cons _ e2 r) (LsCons _ _ x e2 rest r lk)))
    ((Cons _ v vrest)
      (let ((erased hs2) (many hp2) (erased le) (many r) (erased lk)) $ notail $ fit-addrs _ hp rest vrest)
      (let ((erased _) (erased pv2)) (ref-widen _ _ _ le v))
      (let ((many v2)) (coerce v pv2))
      (values hs2 hp2 le (Cons _ v2 r) (LsCons _ _ x v2 rest r lk)))))

(def-fns _ $ (many at-index : (erased (Nat) x) (erased (List $ Nat) f) (subterm many (At x f) p) -> (many (Nat) i))
  (match many p _ ((AtHere _ _) 0) ((AtThere _ _ _ q) (Succ $ notail $ at-index _ _ q))))

; A variable's value: from a frame of values by its place, or, in a group's frame, the member's closure
; made over the group's block.
(def-fns _ $ (many frames-get-plain : (erased (Nat) x) (erased (List $ List $ Nat) ctx) (subterm many (Mem x ctx) p) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Frames (Ref Block hs) ctx) env) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many p _
    ((MHere _ _ _ q)
      (match many env _
        ((FrVals _ _ _ vs lk _)
          (let ((many v) (erased _)) $ at-get _ _ _ q vs lk)
          (values hs hp (le-refl hs) v))
        ((FrGroup _ _ gids g _ _)
          (let ((many i)) $ at-index _ _ q)
          (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ halloc _ hp $ BFn _ g i $ list-nth-or _ gids i (Zero))
          (values hl2 hp2 sf2 v))))
    ((MThere _ _ _ q)
      (match many env _
        ((FrVals _ _ _ _ _ rest) (tail $ frames-get-plain _ _ q _ hp rest))
        ((FrGroup _ _ _ _ _ rest) (tail $ frames-get-plain _ _ q _ hp rest))))))

(def-fns _ $ (many settled-entry-value : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Nat) x) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many (settled-ref _ (heap-entries _ hp) x) _
    ((Some _ v) (values hs hp (le-refl hs) v))
    ((None _) (halloc _ hp $ BError _ "unbound constant"))))

(def-fns _ $ (many slot-eq-answer : (erased (Hist Block) hs) (many (List $ Ref Block hs) args) -> (many (Maybe $ Ref Block hs) r))
  (let-match many args (Cons _ a r1) ((Nil _) (None _)))
  (let-match many r1 (Cons _ b r2) ((Nil _) (None _)))
  (let-match many r2 (Cons _ none r3) ((Nil _) (None _)))
  (let-match many r3 (Cons _ some _) ((Nil _) (None _)))
  (Some _ $ match many (nat-eqb (ref-pos _ _ a) (ref-pos _ _ b)) _ ((BTrue) some) ((BFalse) none)))

(def-fns _ $ (many settled-prim : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Sp) p) (many (List $ Ref Block hs) args) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many args (Cons _ h hidden) ((Nil _) (halloc _ hp $ BError _ "a handle form with no handle")))
  (let ((erased _) (many b) (erased _)) (hread _ hp h))
  (let-match many b (BExt _ pl) (else (halloc _ hp $ BError _ "not a handle")))
  (let-match many pl (PHandle x rd mult shown) (else (halloc _ hp $ BError _ "not a handle")))
  (let-match many (sp-eq p $ SpExpr $ ExSettledErase) (BFalse) ((BTrue) (alloc-ext _ hp $ PHandle x rd (Erased) shown)))
  (let-match many (sp-eq p $ SpExpr $ ExSettledType) (BFalse)
    ((BTrue) (alloc-ext _ hp $ match many rd _ ((MintedIs) (PHandle x (MintedType) (Erased) $ ShText "_")) ((MintedType) (PHandle type-id (MintedIs) (Erased) $ ShText "Type")))))
  (let-match many (sp-eq p $ SpExpr $ ExSettledValue) (BFalse) ((BTrue) (tail $ settled-entry-value _ hp x)))
  (let-match many hidden (Cons _ e r1) ((Nil _) (halloc _ hp $ BError _ "`settled-mult` with no constructors")))
  (let-match many r1 (Cons _ m r2) ((Nil _) (halloc _ hp $ BError _ "`settled-mult` with no constructors")))
  (let-match many r2 (Cons _ u _) ((Nil _) (halloc _ hp $ BError _ "`settled-mult` with no constructors")))
  (values hs hp (le-refl hs) $ match many mult _ ((Erased) e) ((Many) m) ((Once) u)))

(def-fns _ $ (many frames-get : (erased (Nat) x) (erased (List $ List $ Nat) ctx) (subterm many (Mem x ctx) p) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Frames (Ref Block hs) ctx) env) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many p _
    ((MHere _ _ _ q)
      (let-match many env (FrGroup _ _ _ _ grp _) ((FrVals _ _ _ _ _ _) (tail $ frames-get-plain _ _ p _ hp env)))
      (let-match many grp (MkGroup _ _ fns lk))
      (let ((many pr) (erased _)) $ at-get _ _ _ q fns lk)
      (let-match many pr (MkPair _ _ _ fn))
      (let-match many fn (MkAlias _ _ _ _ target) ((MkFunc _ _ _ _ _ _ _ _ _) (tail $ frames-get-plain _ _ p _ hp env)))
      (match many target _
        ((CVar _ _ q2) (tail $ frames-get-plain _ _ q2 _ hp env))
        ((CConst _ t) (tail $ settled-entry-value _ hp t))
        (else (halloc _ hp $ BError _ "internal: an alias with no target"))))
    ((MThere _ _ _ q)
      (match many env _
        ((FrVals _ _ _ _ _ rest) (tail $ frames-get _ _ q _ hp rest))
        ((FrGroup _ _ _ _ _ rest) (tail $ frames-get _ _ q _ hp rest))))))

(def-fns _ $ (many has-branch : (erased (List $ List $ Nat) ctx) (erased (List $ Multiplicity) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) i) -> (many (Bool) r))
  (let-match many bs (Cons _ b rest)
    ((Nil _) (BFalse)))
  (match many b _ ((MkBranch _ _ d _ _) (or (nat-eqb d i) $ tail $ has-branch _ _ rest i))))

(def-fns _ $ (many widen-ref : (erased (Hist Block) a) (erased (Hist Block) b) (erased (Suffix Block b a) le) (many (Ref Block a) r) -> (many (Ref Block b) r2))
  (let ((erased _) (erased p)) (ref-widen _ _ _ le r))
  (coerce r p))

(def-fns _ $ (many widen-refs : (erased (Hist Block) a) (erased (Hist Block) b) (erased (Suffix Block b a) le) (many (List $ Ref Block a) rs) -> (many (List $ Ref Block b) rs2))
  (let ((erased _) (erased p)) (refs-widen _ _ _ le rs))
  (coerce rs p))

; ---- The prelude's constructors the answers are built from, found by name among those the interpreter hands over.

(def-fns _ $ (many pctor : (subterm many (List $ Ctor) env) (many (String) name) -> (many (Ctor) c))
  (let-match many env (Cons _ c rest) ((Nil _) (MkCtor name 0 0 0 (BFalse) (None _) (Nil _) (BFalse))))
  (match many (str-eqb (ctor-name c) name) _ ((BTrue) c) ((BFalse) (tail $ pctor rest name))))

(def-fns _ $ (many field-at : (erased (Hist Block) hs) (many (List $ Ref Block hs) fields) (many (Nat) i) (many (Ref Block hs) v) -> (many (Ref Block hs) r))
  (match many (list-nth _ fields i) _ ((NthHit _ _ _ x _) x) ((NthMiss _ _ _ _) v)))

; ---- Answers into the store: each allocation grows the history, and what was allocated before is widened.

(def-fns _ $ (many store-wrap : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ctor) c) (many (Ref Block hs) r) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (construct _ hp c (Cons _ r (Nil _))))

(def-fns _ $ (many store-wrapped-str : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ctor) c) (many (String) s) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let ((erased _) (many hp1) (erased le1) (many r)) (alloc-ext _ hp (PStr s)))
  (let ((erased h2) (many hp2) (erased le2) (many v)) (store-wrap _ hp1 c r))
  (values h2 hp2 (hist-le-trans _ _ _ le1 le2) v))

(def-fns _ $ (many store-maybe-str : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Maybe $ String) m) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many m _
    ((None _) (construct _ hp (pctor env "None") (Nil _)))
    ((Some _ s) (store-wrapped-str _ hp (pctor env "Some") s))))

(def-fns _ $ (many store-strs : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (List $ String) xs) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many xs (Cons _ x rest) ((Nil _) (construct _ hp (pctor env "Nil") (Nil _))))
  (let ((erased _) (many hp1) (erased le1) (many tl)) (notail $ store-strs env _ hp rest))
  (let ((erased _) (many hp2) (erased le2) (many hd)) (alloc-ext _ hp1 (PStr x)))
  (let ((erased h3) (many hp3) (erased le3) (many v)) (construct _ hp2 (pctor env "Cons") (Cons _ hd (Cons _ (widen-ref _ _ le2 tl) (Nil _)))))
  (values h3 hp3 (hist-le-trans _ _ _ (hist-le-trans _ _ _ le1 le2) le3) v))

(def-fns _ $ (many store-pairs : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (List $ Pair (String) (String)) xs) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many xs (Cons _ x rest) ((Nil _) (construct _ hp (pctor env "Nil") (Nil _))))
  (let-match many x (MkPair _ _ n s))
  (let ((erased _) (many hp1) (erased le1) (many tl)) (notail $ store-pairs env _ hp rest))
  (let ((erased _) (many hp2) (erased le2) (many nr)) (alloc-ext _ hp1 (PStr n)))
  (let ((erased _) (many hp3) (erased le3) (many sr)) (alloc-ext _ hp2 (PStr s)))
  (let ((erased _) (many hp4) (erased le4) (many pr)) (construct _ hp3 (pctor env "MkPair") (Cons _ (widen-ref _ _ le3 nr) (Cons _ sr (Nil _)))))
  (let ((erased le14)) (hist-le-trans _ _ _ (hist-le-trans _ _ _ le1 le2) (hist-le-trans _ _ _ le3 le4)))
  (let ((erased h5) (many hp5) (erased le5) (many v)) (construct _ hp4 (pctor env "Cons") (Cons _ pr (Cons _ (widen-ref _ _ (hist-le-trans _ _ _ (hist-le-trans _ _ _ le2 le3) le4) tl) (Nil _)))))
  (values h5 hp5 (hist-le-trans _ _ _ le14 le5) v))

; A Result: Ok over a value already in the store, or Fail over the message.
(def-fns _ $ (many store-ok : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) r) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (store-wrap _ hp (pctor env "Ok") r))

(def-fns _ $ (many store-fail : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (String) m) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (store-wrapped-str _ hp (pctor env "Fail") m))

(def-fns _ $ (many store-result-str : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Result $ String) r) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many r _
    ((Ok _ s) (store-wrapped-str _ hp (pctor env "Ok") s))
    ((Fail _ m) (store-fail env _ hp m))))

(def-fns _ $ (many store-result-nullary : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (String) ctor) (many (Maybe $ String) failed) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many failed (None _) ((Some _ m) (store-fail env _ hp m)))
  (let ((erased _) (many hp1) (erased le1) (many r)) (construct _ hp (pctor env ctor) (Nil _)))
  (let ((erased h2) (many hp2) (erased le2) (many v)) (store-ok env _ hp1 r))
  (values h2 hp2 (hist-le-trans _ _ _ le1 le2) v))

(def-fns _ $ (many store-result-unit : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Result $ Unit) r) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (store-result-nullary env _ hp "MkUnit" (match many r (((Maybe $ String) _)) ((Ok _ _) (None _)) ((Fail _ m) (Some _ m)))))

(def-fns _ $ (many store-result-kind : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Result $ EntryKind) r) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many r _
    ((Ok _ k) (store-result-nullary env _ hp (match many k (((String) _)) ((IsFile) "IsFile") ((IsDir) "IsDir") ((IsOther) "IsOther") ((Missing) "Missing")) (None _)))
    ((Fail _ m) (store-fail env _ hp m))))

(def-fns _ $ (many store-result-change : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Result $ Change) r) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many r _
    ((Ok _ c) (store-result-nullary env _ hp (match many c (((String) _)) ((Changed) "Changed") ((Unchanged) "Unchanged")) (None _)))
    ((Fail _ m) (store-fail env _ hp m))))

(def-fns _ $ (many store-result-strs : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Result $ List $ String) r) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many r (Ok _ xs) ((Fail _ m) (store-fail env _ hp m)))
  (let ((erased _) (many hp1) (erased le1) (many l)) (store-strs env _ hp xs))
  (let ((erased h2) (many hp2) (erased le2) (many v)) (store-ok env _ hp1 l))
  (values h2 hp2 (hist-le-trans _ _ _ le1 le2) v))

(def-fns _ $ (many store-exts : (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (List $ Payload) ps) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) rs))
  (let-match many ps (Cons _ p rest) ((Nil _) (values hs hp (le-refl hs) (Nil _))))
  (let ((erased _) (many hp1) (erased le1) (many r)) (alloc-ext _ hp p))
  (let ((erased h2) (many hp2) (erased le2) (many rs)) (notail $ store-exts _ hp1 rest))
  (values h2 hp2 (hist-le-trans _ _ _ le1 le2) (Cons _ (widen-ref _ _ le2 r) rs)))

(def-fns _ $ (many store-usage : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Usage) u) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many u (MkUsage a b c d e f g h))
  (let ((erased _) (many hp1) (erased le1) (many rs)) (store-exts _ hp $ Cons _ (PNat a) $ Cons _ (PNat b) $ Cons _ (PNat c) $ Cons _ (PNat d) $ Cons _ (PNat e) $ Cons _ (PNat f) $ Cons _ (PNat g) $ Cons _ (PNat h) $ Nil _))
  (let ((erased h2) (many hp2) (erased le2) (many v)) (construct _ hp1 (pctor env "MkUsage") rs))
  (values h2 hp2 (hist-le-trans _ _ _ le1 le2) v))

(def-fns _ $ (many store-result-exited : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Result $ Exited) r) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many r (Ok _ x) ((Fail _ m) (store-fail env _ hp m)))
  (let-match many x (MkExited code out err))
  (let-match many code (MkU8 n _))
  (let ((erased _) (many hp1) (erased le1) (many rs)) (store-exts _ hp $ Cons _ (PNat n) $ Cons _ (PStr out) $ Cons _ (PStr err) $ Nil _))
  (let ((erased _) (many hp2) (erased le2) (many e)) (construct _ hp1 (pctor env "MkExited") rs))
  (let ((erased h3) (many hp3) (erased le3) (many v)) (store-ok env _ hp2 e))
  (values h3 hp3 (hist-le-trans _ _ _ (hist-le-trans _ _ _ le1 le2) le3) v))

(def-fns _ $ (many store-results : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (List $ Result $ Exited) rs) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many rs (Cons _ r rest) ((Nil _) (construct _ hp (pctor env "Nil") (Nil _))))
  (let ((erased _) (many hp1) (erased le1) (many tl)) (notail $ store-results env _ hp rest))
  (let ((erased _) (many hp2) (erased le2) (many hd)) (store-result-exited env _ hp1 r))
  (let ((erased h3) (many hp3) (erased le3) (many v)) (construct _ hp2 (pctor env "Cons") (Cons _ hd (Cons _ (widen-ref _ _ le2 tl) (Nil _)))))
  (values h3 hp3 (hist-le-trans _ _ _ (hist-le-trans _ _ _ le1 le2) le3) v))

(def-fns _ $ (many exec-disabled : (subterm many (List $ ExecJob) js) -> (many (List $ Result $ Exited) rs))
  (let-match many js (Cons _ j rest) ((Nil _) (Nil _)))
  (let-match many j (MkExecJob prog _ _ _ _))
  (Cons _ (Fail _ $ str-cat prog ": exec is disabled (--no-exec)") $ notail $ exec-disabled rest))

(def-adts $ (RqKind : -> Type)
  enum
  (many RqUnknown : -> (RqKind))
  (many RqWriteOut : -> (RqKind)) (many RqWriteErr : -> (RqKind)) (many RqReadLine : -> (RqKind)) (many RqReadFile : -> (RqKind)) (many RqReadFileIn : -> (RqKind))
  (many RqWriteFile : -> (RqKind)) (many RqGetArgs : -> (RqKind)) (many RqGetEnv : -> (RqKind))
  (many RqGetEnvs : -> (RqKind)) (many RqAppendFile : -> (RqKind)) (many RqReadRemaining : -> (RqKind))
  (many RqListDir : -> (RqKind)) (many RqGetCwd : -> (RqKind)) (many RqStat : -> (RqKind))
  (many RqMkDir : -> (RqKind)) (many RqDeleteFile : -> (RqKind)) (many RqDeleteDir : -> (RqKind))
  (many RqConfinePaths : -> (RqKind)) (many RqConfineOutputBytes : -> (RqKind)) (many RqMeasure : -> (RqKind)) (many RqExec : -> (RqKind)))

(def-adts $ (RqEntry : -> Type)
  enum
  (many MkRqEntry : (many (String) name) (many (RqKind) rq) -> (RqEntry)))

(def-fns _ $ (many rq-cons : (many (String) name) (many (RqKind) rq) (many (List $ RqEntry) rest) -> (many (List $ RqEntry) r))
  (Cons _ (MkRqEntry name rq) rest))

(let ((many request-table))
  $ rq-cons "WriteOut" (RqWriteOut) $
  rq-cons "WriteErr" (RqWriteErr) $ rq-cons "ReadLine" (RqReadLine) $ rq-cons "ReadFile" (RqReadFile) $ rq-cons "ReadFileIn" (RqReadFileIn) $
  rq-cons "WriteFile" (RqWriteFile) $ rq-cons "GetArgs" (RqGetArgs) $ rq-cons "GetEnv" (RqGetEnv) $
  rq-cons "GetEnvs" (RqGetEnvs) $ rq-cons "AppendFile" (RqAppendFile) $ rq-cons "ReadRemaining" (RqReadRemaining) $
  rq-cons "ListDir" (RqListDir) $ rq-cons "GetCwd" (RqGetCwd) $ rq-cons "Stat" (RqStat) $
  rq-cons "MkDir" (RqMkDir) $ rq-cons "DeleteFile" (RqDeleteFile) $ rq-cons "DeleteDir" (RqDeleteDir) $ rq-cons "ConfinePaths" (RqConfinePaths) $
  rq-cons "ConfineOutputBytes" (RqConfineOutputBytes) $ rq-cons "Measure" (RqMeasure) $ rq-cons "Exec" (RqExec) $ Nil _)

(def-fns _ $ (many request-of : (subterm many (List $ RqEntry) es) (many (String) name) -> (many (RqKind) r))
  (let-match many es (Cons _ e rest) ((Nil _) (RqUnknown)))
  (let-match many e (MkRqEntry n rq))
  (match many (str-eqb name n) _
    ((BTrue) rq)
    ((BFalse) (tail $ request-of rest name))))

(let ((many heap-strs-fuel)) 1000000)

(def-fns _ $ (many heap-strs : (many (List $ Ctor) env) (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (List $ String) r))
  (let-match many fuel (Succ k) ((Zero) (Nil _)))
  (let ((erased _) (many hp1) (erased le) (many i) (many fields)) (destruct _ hp (pctor env "Cons") a))
  (let-match many (headed-by i $ pctor env "Cons") (BTrue) ((BFalse) (Nil _)))
  (let ((many a1)) (widen-ref _ _ le a))
  (Cons _ (heap-str _ hp1 $ field-at _ fields 0 a1) $ notail $ heap-strs env k _ hp1 $ field-at _ fields 1 a1))

(def-fns _ $ (many heap-pairs : (many (List $ Ctor) env) (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (List $ Pair (String) (String)) r))
  (let-match many fuel (Succ k) ((Zero) (Nil _)))
  (let ((erased _) (many hp1) (erased le) (many i) (many fields)) (destruct _ hp (pctor env "Cons") a))
  (let-match many (headed-by i $ pctor env "Cons") (BTrue) ((BFalse) (Nil _)))
  (let ((many a1)) (widen-ref _ _ le a))
  (let ((many p)) (field-at _ fields 0 a1))
  (let ((erased _) (many hp2) (erased le2) (many _) (many pf)) (destruct _ hp1 (pctor env "MkPair") p))
  (let ((many p2)) (widen-ref _ _ le2 p))
  (Cons _ (MkPair _ _ (heap-str _ hp2 $ field-at _ pf 0 p2) (heap-str _ hp2 $ field-at _ pf 1 p2)) $ notail $ heap-pairs env k _ hp2 $ widen-ref _ _ le2 $ field-at _ fields 1 a1))

(def-fns _ $ (many heap-maybe-str : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (Maybe $ String) r))
  (let ((erased _) (many hp1) (erased le) (many i) (many fields)) (destruct _ hp (pctor env "Some") a))
  (let-match many (headed-by i $ pctor env "Some") (BTrue) ((BFalse) (None _)))
  (Some _ $ heap-str _ hp1 $ field-at _ fields 0 $ widen-ref _ _ le a))

(def-fns _ $ (many heap-maybe-nat : (many (List $ Ctor) env) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (Maybe $ Nat) r))
  (let ((erased _) (many hp1) (erased le) (many i) (many fields)) (destruct _ hp (pctor env "Some") a))
  (let-match many (headed-by i $ pctor env "Some") (BTrue) ((BFalse) (None _)))
  (Some _ $ heap-nat _ hp1 $ field-at _ fields 0 $ widen-ref _ _ le a))

(def-fns _ $ (many heap-jobs : (many (List $ Ctor) env) (subterm many (Nat) fuel) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (List $ ExecJob) r))
  (let-match many fuel (Succ k) ((Zero) (Nil _)))
  (let ((erased _) (many hp1) (erased le) (many i) (many fields)) (destruct _ hp (pctor env "Cons") a))
  (let-match many (headed-by i $ pctor env "Cons") (BTrue) ((BFalse) (Nil _)))
  (let ((many a1)) (widen-ref _ _ le a))
  (let ((many j)) (field-at _ fields 0 a1))
  (let ((erased _) (many hp2) (erased le2) (many _) (many jf)) (destruct _ hp1 (pctor env "MkExecJob") j))
  (let ((many j2)) (widen-ref _ _ le2 j))
  (Cons _ (MkExecJob (heap-str _ hp2 $ field-at _ jf 0 j2) (heap-strs env heap-strs-fuel _ hp2 $ field-at _ jf 1 j2) (heap-pairs env heap-strs-fuel _ hp2 $ field-at _ jf 2 j2)
      (heap-maybe-str env _ hp2 $ field-at _ jf 3 j2) (heap-str _ hp2 $ field-at _ jf 4 j2))
    $ notail $ heap-jobs env k _ hp2 $ widen-ref _ _ le2 $ field-at _ fields 1 a1))

(def-fns _ $ (many usage-since : (many (Usage) base) (many (Usage) u) -> (many (Usage) r))
  (let-match many base (MkUsage a0 b0 c0 d0 e0 f0 g0 h0))
  (let-match many u (MkUsage a b c d e f g h))
  (MkUsage (nat-sub a a0) (nat-sub b b0) (nat-sub c c0) (nat-sub d d0) (nat-sub e e0) (nat-sub f f0) (nat-sub g g0) (nat-sub h h0)))

(def-fns _ $ (many perform-request : (many (List $ Ctor) env) (many (List $ Ctor) rq) (many (List $ String) pargs) (many (Bool) with-env) (many (Bool) with-exec) (many (Usage) base)
    (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) req) (unique (World) w at vacant-slot) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v) (unique (World) w2 at w))
  (let ((erased h1) (many hp1) (erased le1) (many i) (many fields)) (destruct _ hp (pctor env "WriteOut") req))
  (let ((many req1)) (widen-ref _ _ le1 req))
  (let ((many name)) $ match many i (((String) _)) ((None _) "") ((Some _ j) (match many (list-nth _ rq j) _ ((NthHit _ _ _ c _) (ctor-name c)) ((NthMiss _ _ _ _) ""))))
  (let ((many f0)) (field-at _ fields 0 req1))
  (let ((many s0)) (heap-str _ hp1 f0))
  (let ((many s1)) (heap-str _ hp1 $ field-at _ fields 1 req1))
  (let ((erased (Hist Block) h2) (many (Heap h2) hp2) (erased (Suffix Block h2 h1) le2) (many (Ref Block h2) v) (unique (World) w2))
    (match many (request-of request-table name) (((Hist Block) h2) ((Heap h2) hp2) ((Suffix Block h2 h1) le2) ((Ref Block h2) v) ((World) w2 at w))
      ((RqUnknown)
        (let ((erased h) (many hpx) (erased le) (many a)) $ halloc _ hp1 $ BError _ $ str-cat "cannot interpret the request " name)
        (values h hpx le a w))
      ((RqWriteOut)
        (let ((unique w1) (many _)) (world-do _ w (WriteOut s0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (construct _ hp1 (pctor env "MkUnit") (Nil _)))
        (values h hpx le a w1))
      ((RqWriteErr)
        (let ((unique w1) (many _)) (world-do _ w (WriteErr s0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (construct _ hp1 (pctor env "MkUnit") (Nil _)))
        (values h hpx le a w1))
      ((RqReadLine)
        (let ((unique w1) (many r)) (world-do _ w (ReadLine)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-maybe-str env _ hp1 r))
        (values h hpx le a w1))
      ((RqReadFile)
        (let ((unique w1) (many r)) (world-do _ w (ReadFile s0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-str env _ hp1 r))
        (values h hpx le a w1))
      ((RqReadFileIn)
        (let ((unique w1) (many r)) (world-do _ w (ReadFileIn s0 s1)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-str env _ hp1 r))
        (values h hpx le a w1))
      ((RqWriteFile)
        (let ((unique w1) (many r)) (world-do _ w (WriteFile s0 s1)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-unit env _ hp1 r))
        (values h hpx le a w1))
      ((RqGetArgs)
        (let ((erased h) (many hpx) (erased le) (many a)) (store-strs env _ hp1 pargs))
        (values h hpx le a w))
      ((RqGetEnv)
        (let ((unique w1) (many r)) (world-do _ w (GetEnv s0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-maybe-str env _ hp1 $ match many with-env _ ((BTrue) r) ((BFalse) (None _))))
        (values h hpx le a w1))
      ((RqGetEnvs)
        (let ((unique w1) (many r)) (world-do _ w (GetEnvs)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-pairs env _ hp1 $ match many with-env _ ((BTrue) r) ((BFalse) (Nil _))))
        (values h hpx le a w1))
      ((RqAppendFile)
        (let ((unique w1) (many r)) (world-do _ w (AppendFile s0 s1)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-unit env _ hp1 r))
        (values h hpx le a w1))
      ((RqReadRemaining)
        (let ((unique w1) (many r)) (world-do _ w (ReadRemaining)))
        (let ((erased h) (many hpx) (erased le) (many a)) (alloc-ext _ hp1 (PStr r)))
        (values h hpx le a w1))
      ((RqListDir)
        (let ((unique w1) (many r)) (world-do _ w (ListDir s0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-strs env _ hp1 r))
        (values h hpx le a w1))
      ((RqGetCwd)
        (let ((unique w1) (many r)) (world-do _ w (GetCwd)))
        (let ((erased h) (many hpx) (erased le) (many a)) (alloc-ext _ hp1 (PStr r)))
        (values h hpx le a w1))
      ((RqStat)
        (let ((unique w1) (many r)) (world-do _ w (Stat s0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-kind env _ hp1 r))
        (values h hpx le a w1))
      ((RqMkDir)
        (let ((unique w1) (many r)) (world-do _ w (MkDir s0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-change env _ hp1 r))
        (values h hpx le a w1))
      ((RqDeleteFile)
        (let ((unique w1) (many r)) (world-do _ w (DeleteFile s0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-change env _ hp1 r))
        (values h hpx le a w1))
      ((RqDeleteDir)
        (let ((unique w1) (many r)) (world-do _ w (DeleteDir s0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-change env _ hp1 r))
        (values h hpx le a w1))
      ((RqConfinePaths)
        (let ((unique w1) (many r)) (world-do _ w $ ConfinePaths (heap-strs env heap-strs-fuel _ hp1 f0) (heap-strs env heap-strs-fuel _ hp1 $ field-at _ fields 1 req1)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-unit env _ hp1 r))
        (values h hpx le a w1))
      ((RqConfineOutputBytes)
        (let ((unique w1) (many r)) (world-do _ w (ConfineOutputBytes $ heap-nat _ hp1 f0)))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-result-unit env _ hp1 r))
        (values h hpx le a w1))
      ((RqMeasure)
        (let ((erased _) (many hpc) (erased lec) (many ci) (many _)) (destruct _ hp1 (pctor env "Start") f0))
        (let ((unique w1) (many u)) (world-do _ w $ Measure $ match many (headed-by ci $ pctor env "Start") (((Stopwatch) _)) ((BTrue) (Start)) ((BFalse) (Stop))))
        (let ((erased h) (many hpx) (erased le) (many a)) (store-usage env _ hpc (usage-since base u)))
        (values h hpx (hist-le-trans _ _ _ lec le) a w1))
      ((RqExec)
        (let ((many jobs)) (heap-jobs env heap-strs-fuel _ hp1 $ field-at _ fields 1 req1))
        (let ((unique w1) (many rs)) $ match many with-exec (((World) _ at w) ((List $ Result $ Exited) _))
          ((BTrue)
            (let ((unique w1) (many done)) (world-do _ w $ Exec (heap-maybe-nat env _ hp1 f0) jobs))
            (let-match many done (MkExecResults _ rs _ _ _))
            (values w1 rs))
          ((BFalse) (values w $ exec-disabled jobs)))
        (let ((erased _) (many hp2) (erased le2) (many l)) (store-results env _ hp1 rs))
        (let ((erased h) (many hpx) (erased le3) (many a)) (store-wrap _ hp2 (pctor env "MkExecResults") l))
        (values h hpx (hist-le-trans _ _ _ le2 le3) a w1))))
  (values h2 hp2 (hist-le-trans _ _ _ le1 le2) v w2))

(def-fns _ $ (many no-macro-world : (many (Sp) prim) -> (many (String) msg))
  (str-cat3 "`" (sp-name prim) "` reached with no macro world"))

(def-fns _ $ (many intern-syn : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Sp) prim) (many (List $ Ref Block hs) args) -> (many (Result $ Syn) r))
  (let ((many none)) $ str-cat3 "`" (sp-name prim) "` has no implementation")
  (let-match many args (Cons _ a _) ((Nil _) (Fail _ none)))
  (let ((many p)) $ PosSpot $ NoPos)
  (let-match many (sp-eq prim $ SpExpr $ ExInternNat) (BFalse) ((BTrue) (Ok _ $ RNat p $ heap-nat _ hp a)))
  (let-match many (sp-eq prim $ SpExpr $ ExInternChar) (BFalse)
    ((BTrue) (match many (char-of-nat $ heap-nat _ hp a) _ ((Some _ c) (Ok _ $ RChr p c)) ((None _) (Fail _ "intern-char: a code above 255")))))
  (let-match many (sp-eq prim $ SpExpr $ ExInternString) (BFalse) ((BTrue) (Ok _ $ RString p $ heap-str _ hp a)))
  (Fail _ none))

; ---- Literals (ASSUMPTIONS 51-53, 60): numerals, characters and strings, interned per program into the heap
; a run threads, so that a macro's intern- form mints them where it runs

(def-fns _ $ (many prelude-id : (many (Env) env) (many (String) name) -> (many (Env) r) (many (Nat) x))
  (match many (lookup (env-set-scope env $ env-prelude env) $ NSrc name) _
    ((None _) (values (env-error env $ str-cat "unbound name " $ tick name) $ Zero))
    ((Some _ x) (values env x))))

(def-fns _ $ (many prelude-type : (many (Env) env) (many (String) name) -> (many (Env) r) (many (Term) t))
  (let ((many env2) (many x)) $ prelude-id env name)
  (values env2 $ TApp (TVar x) $ Nil _))

; The bijective spelling of n has digit B1 where n + 1 has bit 0 and B2 where it has bit 1, below its leading one;
; this reads the k bits below index k, most significant first.
(def-fns _ $ (many spell-bits : (many (Nat) b1) (many (Nat) b2) (many (Nat) m) (subterm many (Nat) k) (many (Term) t) -> (many (Term) r))
  (let-match many k (Succ i) ((Zero) t))
  (tail $ spell-bits b1 b2 m i $ TApp (TVar $ match many (nat-bit-test m i) (((Nat) _)) ((Bit0) b1) ((Bit1) b2)) $ Cons _ t $ Nil _))

; The bijective base-2 spelling of a number as a term over the prelude's Bin (section 45).
(def-fns _ $ (many nat-bin-term : (many (Nat) n) (many (Env) env) -> (many (Env) r) (many (Term) t))
  (let ((many env1) (many bz)) $ prelude-id env "BZ")
  (let ((many env2) (many b1)) $ prelude-id env1 "B1")
  (let ((many env3) (many b2)) $ prelude-id env2 "B2")
  (let-match many (nat-bit-length $ Succ n) (Succ k) ((Zero) (values env3 $ TApp (TVar bz) $ Nil _)))
  (values env3 $ spell-bits b1 b2 (Succ n) k $ TApp (TVar bz) $ Nil _))

; ---- The source spelling of a literal, which a printed Nat, Char or String reads back from
; (lib/ffi_core.ml's lit_char and lit_string, lib/literal.ml's spell). The compile-time printer below spells in
; the language; an emitted printer calls Ffi_core (emit.sl).

(def-adts $ (LitKey : -> Type)
  enum
  (many LKSpelled : (many (String) s) -> (LitKey))
  (many LKString : (many (String) body) -> (LitKey)))

(def-fns _ $ (many record-literal : (many (Env) env) (many (LitKey) key) (many (Nat) x) (many (Maybe $ Nat) proof) (many (Syn) node) (many (List $ LitFact) facts) -> (many (Env) r))
  (let-match many (env-literals env) (MkLitTable sp st))
  (let ((many t2)) $ match many key (((LitTable) _)) ((LKSpelled k) (MkLitTable (nm-set _ k x sp) st)) ((LKString k) (MkLitTable sp $ nm-set _ k x st)))
  (env-push-lit (env-set-literals env t2) x proof (Some _ node) facts))

(def-fns _ $ (many lit-lookup : (many (Env) env) (many (LitKey) key) -> (many (Maybe $ Nat) r))
  (let-match many (env-literals env) (MkLitTable sp st))
  (let ((many (NameMap $ Nat) m) (many (String) k)) $ match many key _ ((LKSpelled k) (values sp k)) ((LKString k) (values st k)))
  (match many (nm-get _ k m) _ ((NHit _ _ _ x _) (Some _ x)) ((NMiss _ _ _ _) (None _))))

(def-fns _ $ (many tag-slot : (many (Env) env) (erased (Hist Block) hs) (many (Heap hs) h) (many (Nat) k) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) h2) (erased (Suffix Block hs2 hs) sf) (many (Nat) t))
  (let-match many k (Succ _) ((Zero) (values env hs h (le-refl hs) null-id)))
  (let ((many key)) $ str-cat "slot " $ nat-str k)
  (let-match many (lit-lookup env $ LKSpelled key) (None _) ((Some _ t) (values env hs h (le-refl hs) t)))
  (let ((many env2) (erased hs2) (many h2) (erased sf) (many t)) $ bind-lit env _ h (Many) (BToken _) slot-term (None _))
  (let ((many facts)) $ Cons _ (MkLitFact t slot-term (None _) $ Some _ $ TVar t) $ Nil _)
  (let ((many env3)) $ env-enter-facts env2 facts)
  (let-match many (env-literals env3) (MkLitTable sp st))
  (values (env-push-lit (env-set-literals env3 $ MkLitTable (nm-set _ key t sp) st) t (None _) (None _) facts) hs2 h2 sf t))

; Interns a numeral: a Settled Nat entry outside the scope, found by its text, and an erased Numeral proof
; relating it to its spelling (ASSUMPTIONS 51).
; Interns a numeral: a Settled Nat entry outside the scope, found by its text, and an erased Numeral proof
; relating it to its spelling (ASSUMPTIONS 51).
(def-fns _ $ (many intern-numeral : (many (Env) env) (erased (Hist Block) hs) (many (Heap hs) h) (many (String) key) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) h2) (erased (Suffix Block hs2 hs) sf) (many (Nat) x) (many (Nat) proof))
  (let ((many n)) $ parse-nat key)
  (let ((many env1) (many nat-ty)) $ prelude-type env "Nat")
  (let ((many env2) (erased _) (many hp1) (erased s1) (many x)) $ bind-lit env1 _ h (Many) (BExt _ $ PNat n) nat-ty (None _))
  (let ((many env2b) (many numeral)) $ prelude-id env2 "Numeral")
  (let ((many env2c) (many spelled)) $ nat-bin-term n env2b)
  (let ((many pty)) $ TApp (TVar numeral) $ Cons _ spelled $ Cons _ (TVar x) $ Nil _)
  (let ((many env3) (erased _) (many hp2) (erased s2) (many p)) $ bind-lit env2c _ hp1 (Erased) (BToken _) pty (None _))
  (let ((many env4) (erased h3) (many hp3) (erased s3) (many t)) $ tag-slot env3 _ hp2 n)
  (let ((many facts)) $ Cons _ (MkLitFact x nat-ty (None _) $ Some _ $ slot-atom t) $ Cons _ (MkLitFact p pty (None _) $ None _) $ Nil _)
  (values (record-literal (env-enter-facts env4 facts) (LKSpelled key) x (Some _ p) (RNat (PosSpot $ NoPos) n) facts) h3 hp3 (hist-le-trans _ _ _ s1 $ hist-le-trans _ _ _ s2 s3) x p))

(def-fns _ $ (many lit-proof : (subterm many (List $ LitEntry) lits) (many (Nat) x) -> (many (Maybe $ Nat) r))
  (let-match many lits (Cons _ p rest) ((Nil _) (None _)))
  (let-match many p (MkLitEntry y proof _ _ _))
  (match many (nat-cmp x y) _ ((CEq _ _ _) proof) (else (tail $ lit-proof rest x))))

(def-fns _ $ (many intern-numeral-once : (many (Env) env) (erased (Hist Block) hs) (many (Heap hs) h) (many (String) key) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) h2) (erased (Suffix Block hs2 hs) sf) (many (Nat) x) (many (Nat) proof))
  (let-match many (lit-lookup env $ LKSpelled key) (Some _ x) ((None _) (intern-numeral env _ h key)))
  (values env hs h (le-refl hs) x $ match many (lit-proof (env-lits env) x) _ ((Some _ p) p) ((None _) (Zero))))

(def-fns _ $ (many prelude-missing : (many (Env) env) (many (String) what) (many (String) ty) -> (many (Maybe $ String) r))
  (match many (lookup (env-set-scope env $ env-prelude env) $ NSrc ty) _
    ((Some _ _) (None _))
    ((None _) (Some _ $ str-cat3 what " needs the prelude's " $ str-cat (tick ty) ", which `--no-prelude` leaves out"))))

(def-fns _ $ (many char-key : (many (Char) c) -> (many (String) k))
  (rope-str $ lit-char-rope c))

; Interns a character literal (section 45): (MkChar (MkU8 n p)) over its code's numeral, transparent down
; to the opaque n.
(def-fns _ $ (many intern-char-lit : (many (Env) env) (erased (Hist Block) hs) (many (Heap hs) h) (many (Char) c) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) h2) (erased (Suffix Block hs2 hs) sf))
  (let ((many code)) $ char-code c)
  (let ((many env2) (erased _) (many hp1) (erased s1) (many num) (many np)) $ intern-numeral-once env _ h $ nat-str code)
  (let ((many env2b) (many lt-id)) $ prelude-id env2 "Lt")
  (let ((many env2c) (many modulus)) $ prelude-id env2b "u8-modulus")
  (let ((many lt-ty)) $ TApp (TVar lt-id) $ Cons _ (TVar num) $ Cons _ (TVar modulus) $ Nil _)
  (let ((many env3) (erased _) (many hp2) (erased s2) (many lt)) $ bind-lit env2c _ hp1 (Erased) (BToken _) lt-ty (None _))
  (let ((many env3b) (many mk-char)) $ prelude-id env3 "MkChar")
  (let ((many env3c) (many mk-u8)) $ prelude-id env3b "MkU8")
  (let ((many rule)) $ TApp (TVar mk-char) $ Cons _ (TApp (TVar mk-u8) $ Cons _ (TVar num) $ Cons _ (TVar lt) $ Nil _) $ Nil _)
  (let ((many env3d) (many char-ty)) $ prelude-type env3c "Char")
  (let ((many env4) (erased h3) (many hp3) (erased s3) (many x)) $ bind-lit env3d _ hp2 (Many) (BExt _ $ PNat code) char-ty (Some _ rule))
  (values (record-literal env4 (LKSpelled $ char-key c) x (Some _ np) (RChr (PosSpot $ NoPos) c) $ Cons _ (MkLitFact lt lt-ty (None _) $ None _) $ Cons _ (MkLitFact x char-ty (Some _ rule) $ None _) $ Nil _) h3 hp3 (hist-le-trans _ _ _ s1 $ hist-le-trans _ _ _ s2 s3)))

; Interns a string (ASSUMPTIONS 60): its characters, holding no proof.
(def-fns _ $ (many intern-string-lit : (many (Env) env) (erased (Hist Block) hs) (many (Heap hs) h) (many (String) body) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) h2) (erased (Suffix Block hs2 hs) sf))
  (let ((many env1) (many str-ty)) $ prelude-type env "String")
  (let ((many env2) (erased h1) (many hp1) (erased s1) (many x)) $ bind-lit env1 _ h (Many) (BExt _ $ PStr body) str-ty (None _))
  (values (record-literal env2 (LKString body) x (None _) (RString (PosSpot $ NoPos) body) $ Cons _ (MkLitFact x str-ty (None _) $ None _) $ Nil _) h1 hp1 s1))

(def-fns _ $ (many lit-key : (many (Syn) raw) -> (many (Maybe $ LitKey) k))
  (match many raw _
    ((RNat _ n) (Some _ $ LKSpelled $ nat-str n))
    ((RChr _ c) (Some _ $ LKSpelled $ char-key c))
    ((RString _ s) (Some _ $ LKString s))
    (else (None _))))

; Interns the literal [raw] spells, once per program, into the heap a run threads, so that a macro's intern-
; form mints it where it runs; nothing for anything else.
(def-fns _ $ (many intern-lit : (many (Env) env) (erased (Hist Block) hs) (many (Heap hs) h) (many (Syn) raw) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) h2) (erased (Suffix Block hs2 hs) sf))
  (let-match many (lit-key raw) (Some _ key) ((None _) (values env hs h (le-refl hs))))
  (let-match many (lit-lookup env key) (None _) ((Some _ _) (values env hs h (le-refl hs))))
  (let ((many (String) ty) (many (String) what)) $ match many raw _ ((RNat _ _) (values "Nat" "a numeral")) ((RChr _ _) (values "Char" "a character literal")) (else (values "String" "a string literal")))
  (let-match many (prelude-missing env what ty) (None _) ((Some _ msg) (values (env-error env msg) hs h (le-refl hs))))
  (let-match many raw (RNat _ n)
    ((RChr _ c) (intern-char-lit env _ h c))
    ((RString _ s) (intern-string-lit env _ h s))
    (else (values env hs h (le-refl hs))))
  (let ((many env2) (erased h2) (many hp2) (erased s2) (many _) (many _)) $ intern-numeral env _ h $ nat-str n)
  (values env2 h2 hp2 s2))

(def-fns _ $ (many stand-in : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Nat) x) -> (many (Bool) r))
  (let-match many (settled-ref _ (heap-entries _ hp) x) (Some _ v) ((None _) (BFalse)))
  (let ((erased _) (many b) (erased _)) (hread _ hp v))
  (match many b _ ((BToken _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many resolve-answer : (many (Env) e) (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ref Block hs) args) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many args (Cons _ s r2) ((Nil _) (halloc _ hp $ BError _ "`resolve` with no symbol")))
  (let-match many r2 (Cons _ cs r3) ((Nil _) (halloc _ hp $ BError _ "`resolve` with no constructors")))
  (let-match many r3 (Cons _ ch r4) ((Nil _) (halloc _ hp $ BError _ "`resolve` with no constructors")))
  (let-match many r4 (Cons _ cu _) ((Nil _) (halloc _ hp $ BError _ "`resolve` with no constructors")))
  (let-match many (lookup e $ heap-symbol _ hp s) (Some _ x) ((None _) (values hs hp (le-refl hs) cu)))
  (let ((erased _) (many info)) $ entry e x)
  (let-match many info (MkEInfo _ _ mult st _ _ _ _))
  (let-match many st (SSettled _ _ m) ((SHypothetical _) (values hs hp (le-refl hs) ch)))
  (let-match many (and (env-failed e) $ and (mult-is-many mult) $ stand-in _ hp x) (BFalse) ((BTrue) (values hs hp (le-refl hs) ch)))
  (let ((erased _) (many b) (erased _)) (hread _ hp cs))
  (let-match many b (BCtorFn _ ct) (else (halloc _ hp $ BError _ "`resolve` with no constructor for a Settled")))
  (let ((many shown)) $ match many (lit-shown (env-lits e) m) (((Shown) _)) ((Some _ k) k) ((None _) (ShText $ entry-name-or-id e m)))
  (let ((erased _) (many hp1) (erased s1) (many a)) $ alloc-ext _ hp $ PHandle m (MintedIs) mult shown)
  (let ((erased h2) (many hp2) (erased s2) (many r)) $ halloc _ hp1 $ BTag _ ct $ Cons _ a $ Nil _)
  (values h2 hp2 (hist-le-trans _ _ _ s1 s2) r))

(def-fns _ $ (many heap-denoted : (many (Env) e) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (List $ Term) r))
  (let ((erased _) (many b) (erased _)) (hread _ hp a))
  (let-match many b (BExt _ pl) (else (Nil _)))
  (let-match many pl (PHandle i rd _ _) (else (Nil _)))
  (match many rd _
    ((MintedIs) (Cons _ (TVar i) $ Cons _ (minted-type e i) $ Nil _))
    ((MintedType) (Cons _ (minted-type e i) $ Cons _ type-term $ Nil _))))

(def-fns _ $ (many terms-canon-eq : (many (Env) e) (subterm many (List $ Term) a) (many (List $ Term) b) -> (many (Bool) r))
  (let-match many a (Cons _ s ra) ((Nil _) (match many b _ ((Nil _) (BTrue)) (else (BFalse)))))
  (let-match many b (Cons _ t rb) ((Nil _) (BFalse)))
  (and (term-eq (canon-env e s) (canon-env e t)) $ tail $ terms-canon-eq e ra rb))

(def-fns _ $ (many settled-eq-answer : (many (Env) e) (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ref Block hs) args) -> (many (Maybe $ Ref Block hs) v))
  (let-match many args (Cons _ p r2) ((Nil _) (None _)))
  (let-match many r2 (Cons _ q r3) ((Nil _) (None _)))
  (let-match many r3 (Cons _ none r4) ((Nil _) (None _)))
  (let-match many r4 (Cons _ some _) ((Nil _) (None _)))
  (let ((many snap)) $ comptime-boundary e)
  (Some _ $ match many (terms-canon-eq snap (heap-denoted snap _ hp p) $ heap-denoted snap _ hp q) _ ((BTrue) some) ((BFalse) none)))

(def-fns _ $ (many mint-refused : (many (Env) e) (erased (Hist Block) hs) (many (Heap hs) hp) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let ((erased hl) (many hp2) (erased sf) (many v)) $ halloc _ hp $ BError _ "`mint-settled` with no type handle")
  (values e hl hp2 sf v))

(def-fns _ $ (many mint-mult : (many (Sp) prim) -> (many (Maybe $ Multiplicity) m))
  (let-match many (sp-eq prim $ SpExpr $ ExMintSettled) (BFalse) ((BTrue) (Some _ $ Many)))
  (let-match many (sp-eq prim $ SpExpr $ ExMintSettledErased) (BFalse) ((BTrue) (Some _ $ Erased)))
  (None _))

; mint-settled and mint-settled-erased: a fresh Settled entry outside every scope, of the type the handle
; denotes, holding the value or, when erased, the token, and a handle to it.
(def-fns _ $ (many mint-at : (many (Env) e) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Multiplicity) mult) (many (Term) ty) (many (Maybe $ Term) rule) (many (Maybe $ Ref Block hs) value) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let ((many e2) (many en2) (many x)) $ bind-entry e _ (heap-entries _ hp) (BFalse) (BTrue) (None _) (None _) (BFalse) mult ty rule delegate-id)
  (let ((many hp1)) $ heap-with-entries _ hp en2)
  (let ((erased _) (many hp2) (erased s1) (many a)) $ match many value (((Hist Block) h1) ((Heap h1) p1) ((Suffix Block h1 hs) q1) ((Ref Block h1) b))
    ((Some _ v) (values hs hp1 (le-refl hs) v))
    ((None _) (halloc _ hp1 $ BToken _)))
  (let ((many hp3)) $ heap-with-entries _ hp2 $ entries-set-state _ (heap-entries _ hp2) x $ SSettled _ a x)
  (let ((erased hs4) (many hp4) (erased s4) (many hv)) $ alloc-ext _ hp3 $ PHandle x (MintedIs) mult $ ShText "_")
  (values (env-push-lit e2 x (None _) (None _) $ Cons _ (MkLitFact x ty rule $ None _) $ Nil _) hs4 hp4 (hist-le-trans _ _ _ s1 s4) hv))

(def-fns _ $ (many mint-answer : (many (Env) e) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Multiplicity) mult) (many (List $ Ref Block hs) args) ->
    (many (Env) r) (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many args (Cons _ th r2) ((Nil _) (mint-refused e _ hp)))
  (let-match many (heap-denoted e _ hp th) (Cons _ ty _) ((Nil _) (mint-refused e _ hp)))
  (let-match many mult (Erased) (else
    (let-match many r2 (Cons _ v _)
      ((Nil _)
        (let ((erased hl) (many hp2) (erased sf) (many v)) $ halloc _ hp $ BError _ "`mint-settled` with no value")
        (values e hl hp2 sf v)))
    (mint-at e _ hp mult ty (None _) $ Some _ v)))
  (mint-at e _ hp mult ty (None _) (None _)))

(def-fns _ $ (many handle-id : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) a) -> (many (Maybe $ Pair (Nat) (Multiplicity)) r))
  (let ((erased _) (many b) (erased _)) (hread _ hp a))
  (let-match many b (BExt _ pl) (else (None _)))
  (let-match many pl (PHandle i _ m _) (else (None _)))
  (Some _ $ MkPair _ _ i m))

(def-fns _ $ (many field-refs : (erased (Hist Block) hs) (many (Heap hs) hp) (subterm many (List $ Entry) tele) (many (List $ Ref Block hs) refs) -> (many (List $ Ref Block hs) r))
  (let-match many tele (Cons _ e rest) ((Nil _) (Nil _)))
  (let-match many refs (Cons _ a more) ((Nil _) (Nil _)))
  (let ((many later)) $ notail $ field-refs _ hp rest more)
  (let-match many (mult-eq (entry-mult e) $ Erased) (BFalse) ((BTrue) later))
  (let-match many (handle-id _ hp a) (Some _ im) ((None _) later))
  (let-match many im (MkPair _ _ i _))
  (match many (settled-ref _ (heap-entries _ hp) i) _ ((Some _ v) (Cons _ v later)) ((None _) later)))

(def-fns _ $ (many path-dir : (many (String) path) -> (many (String) dir))
  (let-match many (list-rev _ $ split-on path #\/) (Cons _ _ above) ((Nil _) "."))
  (let-match many above (Cons _ _ _) ((Nil _) "."))
  (let ((many d)) $ join-strs (list-rev _ above) "/")
  (match many (str-is-empty d) _ ((BTrue) "/") ((BFalse) d)))

(def-fns _ $ (many read-target : (many (Env) e) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) here) (many (Ref Block hs) path) -> (many (Result $ Pair (String) (String)) r))
  (let-match many (heap-spot _ hp here) (PosSpot q) (else (Fail _ "no position to read relative to")))
  (let-match many q (MkPos f _ _) ((NoPos) (Fail _ "no position to read relative to")))
  (let-match many (list-mem-str (env-sources e) f) (BTrue) ((BFalse) (Fail _ $ str-cat f ": not a source file or a name given to --comptime-unconfine")))
  (Ok _ $ MkPair _ _ (path-dir f) $ heap-str _ hp path))

(def-fns _ $ (many read-refused : (erased (Hist Block) hs) (many (Heap hs) hp) (unique (World) w at vacant-slot) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v) (unique (World) w2 at w))
  (let ((erased h) (many hpx) (erased le) (many a)) $ halloc _ hp $ BError _ "`read-file` with too few arguments")
  (values h hpx le a w))

(def-fns _ $ (many read-file-answer : (many (Env) e) (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ref Block hs) args) (unique (World) w at vacant-slot) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v) (unique (World) w2 at w))
  (let-match many args (Cons _ here r2) ((Nil _) (read-refused _ hp w)))
  (let-match many r2 (Cons _ path r3) ((Nil _) (read-refused _ hp w)))
  (let-match many r3 (Cons _ okr r4) ((Nil _) (read-refused _ hp w)))
  (let-match many r4 (Cons _ failr _) ((Nil _) (read-refused _ hp w)))
  (let ((erased _) (many b1) (erased _)) (hread _ hp okr))
  (let-match many b1 (BCtorFn _ okc) (else (read-refused _ hp w)))
  (let ((erased _) (many b2) (erased _)) (hread _ hp failr))
  (let-match many b2 (BCtorFn _ failc) (else (read-refused _ hp w)))
  (let ((unique w1) (many r)) $ match many (read-target e _ hp here path) (((World) w1 at w) ((Result $ String) r))
    ((Ok _ dp) (let-match many dp (MkPair _ _ d p)) (world-do _ w (ReadFileIn d p)))
    ((Fail _ m) (values w $ Fail _ m)))
  (let ((erased h3) (many hp3) (erased l3) (many v)) $ match many r (((Hist Block) h3) ((Heap h3) hp3) ((Suffix Block h3 hs) l3) ((Ref Block h3) v)) ((Ok _ s) (store-wrapped-str _ hp okc s)) ((Fail _ m) (store-wrapped-str _ hp failc m)))
  (values h3 hp3 l3 v w1))

(def-adts $ (ApplyParts : ((Hist Block) hs) -> Type)
  enum
  (many MkApplyParts : (erased (Hist Block) hs) (many (Loc) l) (many (Ctor) okc) (many (Ctor) failc) (many (Nat) ci) (many (Multiplicity) mult) (many (List $ Ref Block hs) hrefs) -> (ApplyParts hs)))

(def-fns _ $ (many apply-parts : (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Ref Block hs) args) -> (many (Maybe $ ApplyParts hs) r))
  (let-match many args (Cons _ fr r1) ((Nil _) (None _)))
  (let-match many r1 (Cons _ lr r2) ((Nil _) (None _)))
  (let-match many r2 (Cons _ cr r3) ((Nil _) (None _)))
  (let-match many r3 (Cons _ okr r4) ((Nil _) (None _)))
  (let-match many r4 (Cons _ failr hrefs) ((Nil _) (None _)))
  (let-match many hrefs (Cons _ c _) ((Nil _) (None _)))
  (let ((erased _) (many fb) (erased _)) (hread _ hp fr))
  (let-match many fb (BExt _ fp) (else (None _)))
  (let-match many fp (PStr file) (else (None _)))
  (let ((erased _) (many lb) (erased _)) (hread _ hp lr))
  (let-match many lb (BExt _ lp) (else (None _)))
  (let-match many lp (PNat line) (else (None _)))
  (let ((erased _) (many cb) (erased _)) (hread _ hp cr))
  (let-match many cb (BExt _ cp) (else (None _)))
  (let-match many cp (PNat col) (else (None _)))
  (let ((erased _) (many ob) (erased _)) (hread _ hp okr))
  (let-match many ob (BCtorFn _ okc) (else (None _)))
  (let ((erased _) (many xb) (erased _)) (hread _ hp failr))
  (let-match many xb (BCtorFn _ failc) (else (None _)))
  (let-match many (handle-id _ hp c) (Some _ cm) ((None _) (None _)))
  (let-match many cm (MkPair _ _ ci mult))
  (Some _ $ MkApplyParts _ (MkLoc file $ MkSpot line col) okc failc ci mult hrefs))

(def-fns _ $ (many handle-raws : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Spot) l) (subterm many (List $ Ref Block hs) refs) -> (many (List $ Syn) r))
  (let-match many refs (Cons _ a more) ((Nil _) (Nil _)))
  (let ((many later)) $ notail $ handle-raws _ hp l more)
  (let ((erased _) (many b) (erased _)) (hread _ hp a))
  (let-match many b (BExt _ pl) (else later))
  (let-match many pl (PHandle i rd m shown) (else later))
  (Cons _ (RAtom l $ NHandle i rd m shown) later))

(def-fns _ $ (many oldest-error : (subterm many (List $ Said) ss) (many (Nat) k) (many (Maybe $ Pair (Loc) (String)) found) -> (many (Maybe $ Pair (Loc) (String)) r))
  (let-match many k (Succ k2) ((Zero) found))
  (let-match many ss (Cons _ x rest) ((Nil _) found))
  (let ((many (Maybe $ Pair (Loc) (String)) found2)) $ match many x _ ((SaidError l t) (Some _ $ MkPair _ _ l t)) (else found))
  (tail $ oldest-error rest k2 found2))

(def-lvl macro-lvl)
(def-lvl perform-lvl)

(def-adts $ (ElabWorld : -> Type)
  enum newtype
  (many MkElabWorld : (erased (World) w) (unique (Placed vacant-slot (World) w) p) -> (ElabWorld)))

; The macro world (DESIGN.md section 65): the program store, which an expansion threads and its primitives
; extend where they run. [s] is the slot of the elaborator's world, which the state holds placed at [s] so that
; an expansion gets it back where it was.
(def-adts $ (MacroState : ((Slot) s) -> Type)
  enum
  (many MkMacroState : (erased (Slot) s) (many (Env) e) (erased (ElabWorld) wv) (unique (Placed s (ElabWorld) wv) ew) -> (MacroState s)))

(def-adts $ (Performer : (Type W) ((Nat) x) ((Nat) c) -> Type)
  enum
  (many MkPerformer : (erased Type W) (erased (Nat) x) (erased (Nat) c)
     (many (Fn perform-lvl (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) req) (unique W w) ->
          (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v) (unique W w2 at w)) f)
     (many (Fn perform-lvl (erased (Hist Block) hs) (many (Heap hs) hp) (many (Sp) prim) (many (List $ Ref Block hs) args) (unique W w) ->
          (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (unique W w2 at w)) g)
     -> (Performer W x c))
  (many MkMacroPerformer : (erased (Slot) s) (many (Nat) x) (many (Nat) k)
     (many (Fn perform-lvl (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) req) (unique (MacroState s) w) ->
          (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v) (unique (MacroState s) w2 at w)) f)
     (many (Fn perform-lvl (erased (Hist Block) hs) (many (Heap hs) hp) (many (Sp) prim) (many (List $ Ref Block hs) args) (unique (MacroState s) w) ->
          (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (unique (MacroState s) w2 at w)) g)
     -> (Performer (MacroState s) x (Succ k))))

(def-fns perform-lvl $ (many no-world : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) _req) (unique (Unit) w) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v) (unique (Unit) w2 at w))
  (let ((erased hl2) (many hp2) (erased sf2) (many e)) $ halloc _ hp $ BError _ "`world-do` reached with no world")
  (values hl2 hp2 sf2 e w))

(def-fns perform-lvl $ (many no-prim : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Sp) prim) (many (List $ Ref Block hs) _args) (unique (Unit) w) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (unique (Unit) w2 at w))
  (let ((erased hl2) (many hp2) (erased sf2) (many e)) $ halloc _ hp $ BError _ $ no-macro-world prim)
  (values hl2 hp2 sf2 (Cons _ e $ Nil _) w))

(def-fns _ $ (many error-w : (erased (Hist Block) hs) (many (Heap hs) hp) (many (List $ Multiplicity) ms) (many (String) msg) (erased Type W) (unique W w) -> (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (erased (Picked (Ref Block hs2) ms vs) pk) (unique W w2 at w))
  (let ((erased hl2) (many hp2) (erased sf2) (many vs) (erased pk)) $ error-vals _ hp ms msg)
  (values hl2 hp2 sf2 vs pk w))

(def-fns _ $ (many compile-time : (erased (Nat) x) (erased (Nat) c) -> (many (Performer (Unit) x c) p))
  (MkPerformer _ _ _ no-world no-prim))

(def-fns macro-lvl $ (many macro-no-world : (erased (Slot) s) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) _req) (unique (MacroState s) w) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v) (unique (MacroState s) w2 at w))
  (let ((erased hl2) (many hp2) (erased sf2) (many e)) $ halloc _ hp $ BError _ "`world-do` reached with no world")
  (values hl2 hp2 sf2 e w))

(def-fns macro-lvl $ (many macro-prim : (erased (Slot) s) (erased (Hist Block) hs) (many (Heap hs) hp) (many (Sp) prim) (many (List $ Ref Block hs) args) (unique (MacroState s) w) ->
    (erased (Hist Block) hs2) (many (Heap hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (List $ Ref Block hs2) vs) (unique (MacroState s) w2 at w))
  (let-match unique w (MkMacroState sl e wv ew u))
  (let-match many (sp-eq prim $ SpExpr $ ExGensym) (BFalse)
    ((BTrue)
      (let ((many k)) $ Succ $ env-gensyms e)
      (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ alloc-ext _ hp $ PNat k)
      (values hl2 hp2 sf2 (Cons _ v $ Nil _) $ u sl (env-set-gensyms e k) wv ew)))
  (let-match many (sp-eq prim $ SpExpr $ ExResolve) (BFalse)
    ((BTrue)
      (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ resolve-answer e _ hp args)
      (values hl2 hp2 sf2 (Cons _ v $ Nil _) $ u sl e wv ew)))
  (let-match many (sp-eq prim $ SpExpr $ ExReadFile) (BFalse)
    ((BTrue)
      (let ((unique ew0)) (unplace-at _ _ _ ew))
      (let-match erased (placed-slot _ _ _ ew) (Refl _ _))
      (let-match unique ew0 (MkElabWorld _ pw0))
      (let ((unique w0)) (unplace-at _ _ _ pw0))
      (let-match erased (placed-slot _ _ _ pw0) (Refl _ _))
      (let ((erased hl2) (many hp2) (erased sf2) (many v) (unique w1)) $ read-file-answer e _ hp args w0)
      (values hl2 hp2 sf2 (Cons _ v $ Nil _) $ u sl e _ $ place-at _ $ MkElabWorld _ $ place-at _ w1)))
  (let-match many (sp-eq prim $ SpExpr $ ExSettledEq) (BFalse)
    ((BTrue)
      (let-match many (settled-eq-answer e _ hp args) (Some _ v)
        ((None _)
          (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ halloc _ hp $ BError _ "`settled-eq` with no handles")
          (values hl2 hp2 sf2 (Cons _ v $ Nil _) $ u sl e wv ew)))
      (values hs hp (le-refl hs) (Cons _ v $ Nil _) $ u sl e wv ew)))
  (let-match many (mint-mult prim) (None _)
    ((Some _ mult)
      (let ((many e2) (erased hl2) (many hp2) (erased sf2) (many v)) $ mint-answer e _ hp mult args)
      (values hl2 hp2 sf2 (Cons _ v $ Nil _) $ u sl e2 wv ew)))
  (let-match many (intern-syn _ hp prim args) (Ok _ lit)
    ((Fail _ m)
      (let ((erased hl2) (many hp2) (erased sf2) (many v)) $ halloc _ hp $ BError _ m)
      (values hl2 hp2 sf2 (Cons _ v $ Nil _) $ u sl e wv ew)))
  (let ((many e2) (erased _) (many hp2) (erased sf2)) $ intern-lit e _ hp lit)
  (let ((many x)) $ match many (lit-key lit) (((Nat) x)) ((Some _ key) (match many (lit-lookup e2 key) (((Nat) x)) ((Some _ y) y) ((None _) (Zero)))) ((None _) (Zero)))
  (let ((many shown)) $ match many (lit-shown (env-lits e2) x) (((Shown) t)) ((Some _ t) t) ((None _) (ShText "_")))
  (let ((erased hl3) (many hp3) (erased sf3) (many v)) $ alloc-ext _ hp2 $ PHandle x (MintedIs) (Many) shown)
  (values hl3 hp3 (hist-le-trans _ _ _ sf2 sf3) (Cons _ v $ Nil _) $ u sl e2 wv ew))

; ---- Run-position statements against the environment (section 29): each reads the store out, runs or
; allocates, and puts it back with what holds its addresses widened.

(def-fns _ $ (many heap-set-settled : (erased (Hist Block) hs) (many (Heap hs) h) (many (Nat) x) (many (Ref Block hs) v) -> (many (Heap hs) r))
  (heap-with-entries _ h $ entries-set-state _ (heap-entries _ h) x $ SSettled _ v x))

(def-fns _ $ (many close-members : (many (Env) e) (erased (Hist Block) hs) (many (Heap hs) h) (erased (List $ Nat) gids) (subterm many (List $ Pair (Nat) $ Func gids (Nil (List (Nat)))) fns) (many (Ref Block hs) g) (many (Nat) i) -> (many (Env) r))
  (let-match many fns (Cons _ pr rest) ((Nil _) (env-with-heap e _ h)))
  (let-match many pr (MkPair _ _ x fn))
  (match many fn _
    ((MkFunc _ _ _ _ _ _ _ _ _)
      (let ((erased _) (many h2) (erased sf2) (many v)) $ halloc _ h $ BFn _ g i x)
      (let ((erased _) (erased pg3)) (ref-widen _ _ _ sf2 g))
      (tail $ close-members e _ (heap-set-settled _ h2 x v) _ rest (coerce g pg3) $ Succ i))
    ((MkAlias _ _ _ _ target)
      (let ((many (Maybe $ Nat) t)) $ match many target _ ((CVar _ y _) (Some _ y)) ((CConst _ y) (Some _ y)) (else (None _)))
      (let ((many (Maybe $ Ref Block hs) v)) $ match many t _ ((Some _ y) (settled-ref _ (heap-entries _ h) y)) ((None _) (None _)))
      (let ((many (Heap hs) h2)) $ match many v _ ((Some _ r) (heap-set-settled _ h x r)) ((None _) h))
      (tail $ close-members e _ h2 _ rest g $ Succ i))))

; A run-position def-fns: the group's block over no frames, then a closure block per member.
(def-fns _ $ (many env-close-group : (many (Env) e) (erased (List $ Nat) gids) (many (Group gids (Nil (List (Nat)))) g) -> (many (Env) r))
  (let ((erased _) (many h)) $ env-heap e)
  (let ((erased _) (many h1) (erased _) (many ga)) $ halloc _ h $ BGroup _ _ _ g $ FrNil _)
  (match many g _ ((MkGroup _ _ fns _) (close-members e _ h1 _ fns ga 0))))

; The Settled fields of a value bound to their ids at their declared multiplicities (section 28): a many
; field its address, an erased one the token, a missing one an error block.
(def-fns _ $ (many set-field-states : (erased (Hist Block) hs) (many (Heap hs) h) (subterm many (List $ Nat) fids) (many (List $ Multiplicity) mults) (many (List $ Ref Block hs) vs) ->
    (erased (Hist Block) hs2) (many (Heap hs2) h2))
  (let-match many fids (Cons _ x rest) ((Nil _) (values hs h)))
  (let ((many (Multiplicity) m) (many (List $ Multiplicity) mrest)) $ match many mults _ ((Nil _) (values (Many) $ Nil _)) ((Cons _ m0 mr) (values m0 mr)))
  (let ((many (Block (Ref Block hs)) filler)) $ match many m _ ((Many) (BError _ "missing value"))
    ((Once) (BError _ "missing value")) ((Erased) (BToken _)))
  (let ((many (Maybe $ Ref Block hs) first)) $ match many vs _ ((Nil _) (None _)) ((Cons _ v _) (Some _ v)))
  (let ((many (Maybe $ Ref Block hs) have)) $ match many m _ ((Erased) (None _)) (else first))
  (let ((many (List $ Ref Block hs) vrest)) $ match many (mult-is-many m) _ ((BFalse) vs) ((BTrue) (match many vs (((List $ Ref Block hs) _)) ((Nil _) (Nil _)) ((Cons _ _ vr) vr))))
  (let-match many have (None _)
    ((Some _ v) (tail $ set-field-states _ (heap-set-settled _ h x v) rest mrest vrest)))
  (let ((erased _) (many h2) (erased sf2) (many t)) $ halloc _ h filler)
  (let ((erased _) (erased pr1)) (refs-widen _ _ _ sf2 vrest))
  (tail $ set-field-states _ (heap-set-settled _ h2 x t) rest mrest (coerce vrest pr1)))

; The discriminant of a Settled entry's value under a constructor's reading, or None where it is no Settled or
; its discriminant cannot be read.
(def-fns _ $ (many env-destruct : (many (Env) e) (many (Nat) x) (many (Ctor) ct) -> (many (Env) r) (many (Maybe $ Nat) i))
  (let ((erased _) (many h)) $ env-heap e)
  (let-match many (settled-ref _ (heap-entries _ h) x) (Some _ v) ((None _) (values e $ None _)))
  (let ((erased _) (many h2) (erased _) (many i) (many _)) $ destruct _ h ct v)
  (values (env-with-heap e _ h2) i))

(def-fns _ $ (many env-set-fields : (many (Env) e) (many (Nat) x) (many (Ctor) ct) (many (List $ Nat) fids) (many (List $ Multiplicity) mults) -> (many (Env) r))
  (let ((erased _) (many h)) $ env-heap e)
  (let-match many (settled-ref _ (heap-entries _ h) x) (Some _ v) ((None _) e))
  (let ((erased _) (many h2) (erased _) (many _) (many fs)) $ destruct _ h ct v)
  (let ((erased _) (many h3)) $ set-field-states _ h2 fids mults fs)
  (env-with-heap e _ h3))

(def-fns _ $ (many env-set-tokens : (many (Env) e) (subterm many (List $ Nat) ids) -> (many (Env) r))
  (match many ids _
    ((Nil _) e)
    ((Cons _ x rest) (tail $ env-set-tokens (set-state-closed e x $ BToken _) rest))))

(def-fns _ $ (many widen-en : (erased (Hist Block) a) (erased (Hist Block) b) (erased (Suffix Block b a) le) (many (IdMap $ EInfo a) en) -> (many (IdMap $ EInfo b) en2))
  (let ((many en2) (many _)) (store-grow _ _ le en (Nil _)))
  en2)

(def-fns _ $ (many error-of : (erased (Hist Block) hs) (many (Heap hs) hp) (many (Ref Block hs) v) -> (many (Maybe $ String) m))
  (let ((erased _) (many b) (erased _)) (hread hs hp v))
  (match many b _ ((BError _ m) (Some _ m)) (else (None _))))

