; self/eval.sl -- the compile-time interpreter (KERNEL.md's round trip; lib/eval.ml): a plain recursive
; evaluator over post-erasure code and the store of self/heap.sl, bounded by a fuel that decreases along the
; call stack so the checker accepts it. Every value is an address; every step returns the grown store with
; a proof of the growth, by which what was held before is widened. Extern functions run as the host's own
; (section 41).

(def-fns _ $ erased le-refl : (erased (Nat) a) -> (erased (Lt a (Succ a)) p)
  (lt-succ a))

(def-fns _ $ erased le-step : (erased (Nat) a) (erased (Nat) b) (erased (Lt a (Succ b)) p) -> (erased (Lt a (Succ (Succ b))) q)
  (lt-weaken a (Succ b) p))

; What runs under: the Const entries the code names and the frames it binds.
(def-adts $ St : ((Nat) a) ((List $ List $ Bin) ctx) -> Type
  enum
  (many MkSt : (erased (Nat) a) (erased (List $ List $ Bin) ctx) (many (IdMap $ EInfo a) consts) (many (Frames a ctx) env) -> (St a ctx)))

(def-fns _ $ many st-weaken : (erased (Nat) b) (erased (Nat) c) (erased (Lt b (Succ c)) le) (erased (List $ List $ Bin) ctx) (many (St b ctx) st) -> (many (St c ctx) r)
  (match many st _ ((MkSt a cx cs env) (MkSt _ _ (entries-weaken b c le cs) (frames-weaken b c le cx env)))))

(def-fns _ $ many st-consts : (erased (Nat) a) (erased (List $ List $ Bin) ctx) (many (St a ctx) st) -> (many (IdMap $ EInfo a) r)
  (match many st _ ((MkSt z cx cs env) cs)))

(def-fns _ $ many st-push : (erased (Nat) a) (erased (List $ List $ Bin) ctx) (many (St a ctx) st) (many (List $ Bin) f) (many (List $ Addr a) vs) (erased (Lockstep (Bin) (Addr a) f vs) lk) -> (many (St a (Cons (List (Bin)) f ctx)) r)
  (match many st _ ((MkSt z cx cs env) (MkSt _ _ cs $ FrVals _ _ f vs lk env))))

; ---- Extern values (section 41; lib/ffi_core.ml): payload blocks, read and made through the store

(def-fns _ $ many heap-nat : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Addr hs) a) -> (many (Nat) n)
  (let (erased x) (erased lt) (many b) $ deref Block _ hp a)
  (match many b _ ((BExt z p) (match many p _ ((PNat n) n) (else 0))) (else 0)))

(def-fns _ $ many heap-bin : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Addr hs) a) -> (many (Bin) n)
  (let (erased x) (erased lt) (many b) $ deref Block _ hp a)
  (match many b _ ((BExt z p) (match many p _ ((PBin r) r) (else (BZ)))) (else (BZ))))

(def-fns _ $ many heap-str : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Addr hs) a) -> (many (String) n)
  (let (erased x) (erased lt) (many b) $ deref Block _ hp a)
  (match many b _ ((BExt z p) (match many p _ ((PStr s) s) (else (SNil)))) (else (SNil))))

(def-fns _ $ many alloc-ext : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Payload) p) -> (many (Heap Block (Succ hs)) hp2) (many (Addr (Succ hs)) a)
  (alloc Block _ hp $ BExt _ p))

(def-fns _ $ many field-nat : (erased (Nat) hs) (many (Heap Block hs) hp) (many (List $ Addr hs) fields) (many (Nat) i) -> (many (Nat) n)
  (match many (list-nth _ fields i) _ ((NthHit nt nl ni x np) (heap-nat _ hp x)) ((NthMiss nt nl ni np) 0)))

(def-fns _ $ many ext-construct : (erased (Nat) hs) (many (Heap Block hs) hp) (many (ExtType) ext) (many (Nat) index) (many (List $ Addr hs) fields) -> (many (Heap Block (Succ hs)) hp2) (many (Addr (Succ hs)) a)
  (let (many (Payload) p)
    (match many ext _
      ((ExtNat) (PNat $ match many index (((Nat) n)) ((Zero) (Zero)) ((Succ k) (Succ $ field-nat _ hp fields 0))))
      ((ExtBin)
        (let (many (Bin) rest) $ match many (list-nth _ fields 0) _ ((NthHit nt nl ni x np) (heap-bin _ hp x)) ((NthMiss nt nl ni np) (BZ)))
        (PBin $ match many index (((Bin) b)) ((Zero) (BZ)) ((Succ k) (match many k (((Bin) b)) ((Zero) (B1 rest)) ((Succ k2) (B2 rest))))))
      ((ExtString)
        (let (many (String) rest) $ match many (list-nth _ fields 1) _ ((NthHit nt nl ni x np) (heap-str _ hp x)) ((NthMiss nt nl ni np) (SNil)))
        (PStr $ match many index (((String) s)) ((Zero) (SNil)) ((Succ k) (SCons (char-of-code $ field-nat _ hp fields 0) rest))))))
  (alloc-ext _ hp p))

(def-fns _ $ many ext-destruct : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Payload) p) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Nat) index) (many (List $ Addr hs2) fields)
  (match many p _
    ((PNat n)
      (match many n _
        ((Zero) (values hs hp (le-refl hs) 0 $ Nil _))
        ((Succ k)
          (let (many hp2) (many a) $ alloc-ext _ hp $ PNat k)
          (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) 1 $ Cons _ a $ Nil _))))
    ((PBin b)
      (match many b _
        ((BZ) (values hs hp (le-refl hs) 0 $ Nil _))
        ((B1 r)
          (let (many hp2) (many a) $ alloc-ext _ hp $ PBin r)
          (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) 1 $ Cons _ a $ Nil _))
        ((B2 r)
          (let (many hp2) (many a) $ alloc-ext _ hp $ PBin r)
          (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) 2 $ Cons _ a $ Nil _))))
    ((PStr s)
      (match many s _
        ((SNil) (values hs hp (le-refl hs) 0 $ Nil _))
        ((SCons c rest)
          (let (many hp2) (many a1) $ alloc-ext _ hp $ PNat $ char-code c)
          (let (many hp3) (many a2) $ alloc-ext _ hp2 $ PStr rest)
          (values (Succ (Succ hs)) hp3 (le-step _ _ $ le-step _ _ $ le-refl hs) 1 $ Cons _ (addr-weaken _ _ (le-step _ _ $ le-refl _) a1) $ Cons _ a2 $ Nil _))))))

; ---- Constructing and taking apart (section 38): an untagged value is its many fields, one of them bare,
; none the token; a block's fields, bounded by its address, widen to the store's size.

(def-fns _ $ many tuple : (erased (Nat) hs) (many (Heap Block hs) hp) (many (List $ Addr hs) vs) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Addr hs2) v)
  (match many vs _
    ((Nil a)
      (let (many hp2) (many v) $ alloc Block _ hp $ BToken _)
      (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) v))
    ((Cons a v rest)
      (match many rest _
        ((Nil b) (values hs hp (le-refl hs) v))
        ((Cons b w rest2)
          (let (many hp2) (many t) $ alloc Block _ hp $ BTup _ vs)
          (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) t))))))

(def-fns _ $ many untuple : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Nat) n) (many (Addr hs) v) -> (many (List $ Addr hs) vs)
  (match many n _
    ((Zero) (Nil _))
    ((Succ k)
      (match many k _
        ((Zero) (Cons _ v $ Nil _))
        ((Succ k2)
          (let (erased a) (erased lt) (many b) $ deref Block _ hp v)
          (match many b _
            ((BTup z fs) (addrs-weaken _ _ (lt-weaken _ _ lt) fs)) (else (Nil $ Addr hs))))))))

(def-fns _ $ many construct : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Ctor) c) (many (List $ Addr hs) args) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Addr hs2) v)
  (match many c _
    ((MkCtor name id index arity tagged ext shape)
      (match many ext _
        ((Some a e)
          (let (many hp2) (many v) $ ext-construct _ hp e index args)
          (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) v))
        ((None a)
          (match many tagged _
            ((BTrue)
              (let (many hp2) (many v) $ alloc Block _ hp $ BTag _ c args)
              (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) v))
            ((BFalse) (tuple _ hp args))))))))

; A value's discriminant and many fields where the FFI holds the type or a tag says (section 38); None
; otherwise, the value then being its fields as they stand.
(def-fns _ $ many dispatch : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Maybe $ ExtType) ext) (many (Bool) tagged) (many (Addr hs) v) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Maybe $ Pair (Nat) $ List $ Addr hs2) r)
  (let (erased a) (erased lt) (many b) $ deref Block _ hp v)
  (match many b _
    ((BExt z p)
      (match many ext _
        ((None e) (values hs hp (le-refl hs) $ None _))
        ((Some e t)
          (let (erased hs2) (many hp2) (erased le) (many i) (many fs) $ ext-destruct _ hp p)
          (values hs2 hp2 le $ Some _ $ MkPair _ _ i fs))))
    ((BTag z ct fs)
      (match many tagged _
        ((BTrue) (values hs hp (le-refl hs) $ Some _ $ MkPair _ _ (ctor-index ct) $ addrs-weaken _ _ (lt-weaken _ _ lt) fs))
        ((BFalse) (values hs hp (le-refl hs) $ None _))))
    (else (values hs hp (le-refl hs) $ None _))))

(def-fns _ $ many destruct : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Ctor) c) (many (Addr hs) v) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Nat) i) (many (List $ Addr hs2) fields)
  (match many c _
    ((MkCtor name id index arity tagged ext shape)
      (let (erased hs2) (many hp2) (erased le) (many read) $ dispatch _ hp ext tagged v)
      (match many read _
        ((Some a p) (match many p _ ((MkPair x y i fs) (values hs2 hp2 le i fs))))
        ((None a) (values hs2 hp2 le index $ untuple _ hp2 arity $ addr-weaken _ _ le v))))))

(def-fns _ $ many ctor-at : (many (Adt) adt) (many (Nat) i) -> (many (Maybe $ Ctor) c)
  (match many (list-nth _ (adt-ctors adt) i) _ ((NthHit nt nl ni c np) (Some _ c)) ((NthMiss nt nl ni np) (None _))))

(def-fns _ $ many vnat : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Nat) n) -> (many (Heap Block (Succ hs)) hp2) (many (Addr (Succ hs)) a)
  (alloc-ext _ hp $ PNat n))

; A Rope value read back for the host's flatten (ASSUMPTIONS 122); the recursion into a block's fields is
; bounded by the address, which a field's smaller number refines.
(def-fns _
  (many rope-walk : (subterm erased (Nat) fuel) (subterm many (Bin) path) (erased (Nat) hs) (many (Heap Block hs) hp) (erased (Nat) n) (erased (Numeral path n) sp) (erased (Lt n hs) lt) (erased (Lt n fuel) lf) -> (many (Rope) r)
    (match erased fuel _
      (absurd (Zero) (lt-zero n lf))
      ((Succ k)
        (match many (deref-path Block _ hp path n sp lt) _
          ((BExt z p) (match many p _ ((PStr s) (RStr s)) ((PNat m) (RChar $ char-of-code m)) (else (REmpty))))
          ((BTag z ct fields) (rope-fields k _ hp n lt lf fields))
          (else (REmpty))))))
  (many rope-fields : (subterm erased (Nat) fuel) (erased (Nat) hs) (many (Heap Block hs) hp) (erased (Nat) a) (erased (Lt a hs) lt) (erased (Lt a (Succ fuel)) lf) (subterm many (List $ Addr a) fs) -> (many (Rope) r)
    (match many fs _
      ((Nil t) (REmpty))
      ((Cons t f rest)
        (let-match many f (MkAddr bd nf pf spf ltf))
        (RCat (rope-walk fuel pf _ hp nf spf (lt-le-trans nf a hs ltf (lt-weaken a hs lt)) (lt-le-trans nf a fuel ltf lf)) (rope-fields fuel _ hp a lt lf rest))))))

(def-fns _ $ many flatten-value : (erased (Nat) hs) (many (Heap Block hs) hp) (many (Addr hs) a) -> (many (String) s)
  (let-match many a (MkAddr bd n path sp lt))
  (let (many s) (erased p) $ flatten $ rope-walk _ path _ hp n sp lt (lt-succ n))
  s)

; An extern function over its arguments, or None where the model runs instead: nat-cmp builds a plain
; ADT (ASSUMPTIONS 120). The arguments are counted against the arity here, the call having been checked
; against the model's telescope.
(def-fns _ $ many apply-extern : (erased (Nat) n) (many (Extern n) e) (erased (Nat) hs) (many (Heap Block hs) hp) (many (List $ Addr hs) args) -> (many (Heap Block (Succ hs)) hp2) (many (Maybe $ Addr (Succ hs)) r)
  (let (many (Maybe $ Addr hs) a) $ match many (list-nth _ args 0) _ ((NthHit nt nl ni x np) (Some _ x)) ((NthMiss nt nl ni np) (None _)))
  (let (many (Maybe $ Addr hs) b) $ match many (list-nth _ args 1) _ ((NthHit nt nl ni x np) (Some _ x)) ((NthMiss nt nl ni np) (None _)))
  (let (many (Nat) na) $ match many a _ ((Some t x) (heap-nat _ hp x)) ((None t) 0))
  (let (many (Nat) nb) $ match many b _ ((Some t x) (heap-nat _ hp x)) ((None t) 0))
  (let (many (String) sa) $ match many a _ ((Some t x) (heap-str _ hp x)) ((None t) (SNil)))
  (let (many (String) sb) $ match many b _ ((Some t x) (heap-str _ hp x)) ((None t) (SNil)))
  (let (many (Payload) p)
    (match many e _
      ((ExAdd) (PNat $ nat-add na nb))
      ((ExNatCmp) (PNat 0))
      ((ExNatMod)
        (match many (lt-dec (Zero) nb) (((Payload) q))
          ((Yes x y pos) (let (many m) (erased pf) (erased pq) $ nat-mod na nb pos) (PNat m))
          ((No x y q) (PStr "nat-mod: zero modulus"))))
      ((ExBinToNat)
        (let (many n2) (erased pf) $ bin-to-nat $ match many a (((Bin) r)) ((Some t x) (heap-bin _ hp x)) ((None t) (BZ)))
        (PNat n2))
      ((ExTrim) (PStr $ trim sa))
      ((ExAppend) (PStr $ str-append sa sb))
      ((ExFlatten) (PStr $ match many a (((String) r)) ((Some t x) (flatten-value _ hp x)) ((None t) (SNil))))))
  (let (many hp2) (many v) $ alloc-ext _ hp p)
  (values hp2 $ match many e (((Maybe $ Addr (Succ hs)) r)) ((ExNatCmp) (None _)) (else (Some _ v))))

; ---- Values at every position of a code's index (ASSUMPTIONS 125)

(def-fns _ $ many vals-of : (erased (Nat) hs) (subterm many (List $ Mult) ms) (many (Addr hs) v) -> (many (Vals hs ms) r)
  (match many ms _
    ((Nil a) (ValsNil _))
    ((Cons a m rest) (match many m _ ((Many) (ValsMany _ _ v $ vals-of _ rest v)) ((Erased) (ValsErased _ _ $ vals-of _ rest v))))))

(def-fns _ $ many error-vals : (erased (Nat) hs) (many (Heap Block hs) hp) (many (List $ Mult) ms) (many (String) msg) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Vals hs2 ms) vs)
  (let (many hp2) (many e) $ alloc Block _ hp $ BError _ msg)
  (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) $ vals-of _ ms e))

; Cut or padded to the index, a closure's arity being a runtime property; a missing value is an error block.
(def-fns _ $ many vals-fit : (erased (Nat) hs) (many (Heap Block hs) hp) (subterm many (List $ Mult) ms) (many (List $ Addr hs) vs) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Vals hs2 ms) r)
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
              (let (many hp2) (many e) $ alloc Block _ hp $ BError _ "arity mismatch")
              (let (erased hs3) (many hp3) (erased le3) (many r) $ vals-fit _ hp2 rest $ Nil _)
              (values hs3 hp3 (le-trans _ _ _ (le-step _ _ $ le-refl hs) le3) $ ValsMany _ _ (addr-weaken _ _ le3 e) r))
            ((Cons b v vrest)
              (let (erased hs2) (many hp2) (erased le) (many r) $ vals-fit _ hp rest vrest)
              (values hs2 hp2 le $ ValsMany _ _ (addr-weaken _ _ le v) r))))))))

(def-fns _ $ many vals-list : (erased (Nat) hs) (erased (List $ Mult) ms) (subterm many (Vals hs ms) vs) -> (many (List $ Addr hs) r)
  (match many vs _
    ((ValsNil a) (Nil _))
    ((ValsMany a m v rest) (Cons _ v $ vals-list _ _ rest))
    ((ValsErased a m rest) (vals-list _ _ rest))))

(def-fns _ $ many vals-one : (erased (Nat) hs) (many (Vals hs many-one) vs) -> (many (Addr hs) v)
  (match many vs _ ((ValsMany a m v rest) v)))

; The many values of [vs] as the frame of the ids picked from the same positions.
(def-fns _ $ many vals-frame : (erased (Nat) hs) (erased (List $ Mult) ms) (erased (List $ Bin) ids) (erased (Picked (Bin) ms ids) pk) (subterm many (Vals hs ms) vs) -> (many (List $ Addr hs) r) (erased (Lockstep (Bin) (Addr hs) ids r) lk)
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
(def-fns _ $ many fit-addrs : (erased (Nat) hs) (many (Heap Block hs) hp) (subterm many (List $ Bin) ids) (many (List $ Addr hs) vs) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (List $ Addr hs2) r) (erased (Lockstep (Bin) (Addr hs2) ids r) lk)
  (match many ids _
    ((Nil a) (values hs hp (le-refl hs) (Nil _) (LsNil _ _)))
    ((Cons a x rest)
      (match many vs _
        ((Nil b)
          (let (many hp2) (many e) $ alloc Block _ hp $ BError _ "arity mismatch")
          (let (erased hs3) (many hp3) (erased le3) (many r) (erased lk) $ fit-addrs _ hp2 rest $ Nil _)
          (let (many e2) $ addr-weaken _ _ le3 e)
          (values hs3 hp3 (le-trans _ _ _ (le-step _ _ $ le-refl hs) le3) (Cons _ e2 r) (LsCons _ _ x e2 rest r lk)))
        ((Cons b v vrest)
          (let (erased hs2) (many hp2) (erased le) (many r) (erased lk) $ fit-addrs _ hp rest vrest)
          (let (many v2) $ addr-weaken _ _ le v)
          (values hs2 hp2 le (Cons _ v2 r) (LsCons _ _ x v2 rest r lk)))))))

(def-fns _ $ many at-index : (erased (Bin) x) (erased (List $ Bin) f) (subterm many (At x f) p) -> (many (Nat) i)
  (match many p _ ((AtHere y rest) 0) ((AtThere y z rest q) (Succ $ at-index _ _ q))))

; A variable's value: from a frame of values by its place, or, in a group's frame, the member's closure
; made over the group's block.
(def-fns _ $ many frames-get : (erased (Bin) x) (erased (List $ List $ Bin) ctx) (subterm many (Mem x ctx) p) (erased (Nat) hs) (many (Heap Block hs) hp) (many (Frames hs ctx) env) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Addr hs2) v)
  (match many p _
    ((MHere y f c q)
      (match many env _
        ((FrVals a c2 f2 vs lk rest)
          (let (many v) (erased sq) $ at-get _ _ _ q vs lk)
          (values hs hp (le-refl hs) v))
        ((FrGroup a c2 gids g rest)
          (let (many i) $ at-index _ _ q)
          (let (many hp2) (many v) $ alloc Block _ hp $ BFn _ g i $ list-nth-or _ gids i (BZ))
          (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) v))))
    ((MThere y f c q)
      (match many env _
        ((FrVals a c2 f2 vs lk rest) (frames-get _ _ q _ hp rest))
        ((FrGroup a c2 gids g rest) (frames-get _ _ q _ hp rest))))))

(def-fns _ $ many has-branch : (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) i) -> (many (Bool) r)
  (match many bs _
    ((Nil a) (BFalse))
    ((Cons a b rest) (match many b _ ((MkBranch c n0 d ids body) (or (nat-eq d i) $ has-branch _ _ rest i))))))

(def-fns _ $ many error-list : (erased (Nat) hs) (many (Heap Block hs) hp) (many (String) msg) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (List $ Addr hs2) vs)
  (let (many hp2) (many e) $ alloc Block _ hp $ BError _ msg)
  (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) $ Cons _ e $ Nil _))

(def-fns _
  (many eval : (subterm many (Nat) fuel) (erased (Nat) hs) (many (Heap Block hs) hp) (erased (List $ List $ Bin) ctx) (erased (List $ Mult) ms) (subterm many (Code ctx ms) code) (many (St hs ctx) st) ->
      (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Vals hs2 ms) vs)
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
        (let (many hp2) (many a) $ alloc Block _ hp $ block-weaken _ _ (LtZ hs) v)
        (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) $ ValsMany _ _ a $ ValsNil _))
      ((CErased c ms2)
        (let (many hp2) (many a) $ alloc Block _ hp $ BToken _)
        (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) $ vals-of _ ms2 a))
      ((CValues c ms2 cs2 pk) (eval-picked fuel _ hp _ cs2 ms2 pk st))
      ((CApp c ms2 f args cc)
        (let (erased h1) (many hp1) (erased le1) (many fvs) $ eval fuel _ hp _ _ f st)
        (let (erased h2) (many hp2) (erased le2) (many avs) $ eval-list fuel _ hp1 _ args $ st-weaken _ _ le1 _ st)
        (let (many fv) $ addr-weaken _ _ le2 $ vals-one _ fvs)
        (match many fuel _
          ((Zero)
            (let (erased h3) (many hp3) (erased le3) (many r) $ error-vals _ hp2 ms2 "out of fuel")
            (values h3 hp3 (le-trans _ _ _ (le-trans _ _ _ le1 le2) le3) r))
          ((Succ k)
            (let (erased h3) (many hp3) (erased le3) (many rs) $ apply k _ hp2 (entries-weaken _ _ (le-trans _ _ _ le1 le2) $ st-consts _ _ st) fv avs)
            (let (erased h4) (many hp4) (erased le4) (many r) $ vals-fit _ hp3 ms2 rs)
            (values h4 hp4 (le-trans _ _ _ (le-trans _ _ _ le1 le2) (le-trans _ _ _ le3 le4)) r))))
      ((CLet c ms2 ns ids pk rhs rest)
        (let (erased h1) (many hp1) (erased le1) (many rvs) $ eval fuel _ hp _ _ rhs st)
        (let (many vs) (erased lk) $ vals-frame _ _ _ pk rvs)
        (let (erased h2) (many hp2) (erased le2) (many r) $ eval fuel _ hp1 _ _ rest $ st-push _ _ (st-weaken _ _ le1 _ st) ids vs lk)
        (values h2 hp2 (le-trans _ _ _ le1 le2) r))
      ((CLetRec c ns gids g rest)
        (match many st _
          ((MkSt a cx cs env)
            (match many g _
              ((MkGroup c1 ids fns lk)
                (let (many hp1) (many ga) $ alloc Block _ hp $ BGroup _ _ _ g env)
                (let (erased le1) (le-step _ _ $ le-refl hs))
                (let (erased h2) (many hp2) (erased le2) (many r) $ eval fuel _ hp1 _ _ rest $ MkSt _ _ (entries-weaken _ _ le1 cs) (FrGroup _ _ ids ga $ frames-weaken _ _ le1 _ env))
                (values h2 hp2 (le-trans _ _ _ le1 le2) r))))))
      ((CMatch c ns scrut shape branches dfl live)
        (let (erased h1) (many hp1) (erased le1) (many svs) $ eval fuel _ hp _ _ scrut st)
        (let (many v) $ vals-one _ svs)
        (let (many st1) $ st-weaken _ _ le1 _ st)
        (let (erased (Nat) h2) (many (Heap Block h2) hp2) (erased (Lt h1 (Succ h2)) le2) (many (Maybe $ Pair (Nat) $ List $ Addr h2) read)
          (match many shape _
            ((ShKnown c2 adt) (dispatch _ hp1 (adt-ext adt) (adt-tagged adt) v))
            ((ShNone c2) (values h1 hp1 (le-refl h1) $ None _))
            ((ShHeld c2 mcode held)
              (let (erased h1b) (many hp1b) (erased le1b) (many mvs) $ eval fuel _ hp1 _ _ mcode st1)
              (let (erased ma) (erased mlt) (many mb) $ deref Block _ hp1b $ vals-one _ mvs)
              (match many mb (((Nat) h) ((Heap Block h) p) ((Lt h1 (Succ h)) l) ((Maybe $ Pair (Nat) $ List $ Addr h) r))
                ((BMat z a)
                  (let (erased h1c) (many hp1c) (erased le1c) (many r) $ dispatch _ hp1b (adt-ext a) (adt-tagged held) $ addr-weaken _ _ le1b v)
                  (values h1c hp1c (le-trans _ _ _ le1b le1c) r))
                (else (values h1b hp1b le1b $ None _))))))
        (let (many st2) $ st-weaken _ _ le2 _ st1)
        (let (many v2) $ addr-weaken _ _ le2 v)
        (let (erased (Nat) h3) (many (Heap Block h3) hp3) (erased (Lt h2 (Succ h3)) le3) (many (Vals h3 ns) r)
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
                      (let (erased h2c) (many hp2c) (erased le2c) (many r) $ eval fuel _ hp2b _ _ body $ st-push _ _ (st-weaken _ _ le2b _ st2) ids fs lk)
                      (values h2c hp2c (le-trans _ _ _ le2b le2c) r))))))))
        (values h3 hp3 (le-trans _ _ _ (le-trans _ _ _ le1 le2) le3) r))
      ((CAbsurd c ms2) (error-vals _ hp ms2 "absurd code reached"))
      ((CError c ms2 m) (error-vals _ hp ms2 m))))

  (many eval-list : (subterm many (Nat) fuel) (erased (Nat) hs) (many (Heap Block hs) hp) (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) (many (St hs ctx) st) ->
      (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (List $ Addr hs2) vs)
    (match many cs _
      ((Nil a) (values hs hp (le-refl hs) $ Nil _))
      ((Cons a c rest)
        (let (erased h1) (many hp1) (erased le1) (many vs1) $ eval fuel _ hp _ _ c st)
        (let (erased h2) (many hp2) (erased le2) (many vs) $ eval-list fuel _ hp1 _ rest $ st-weaken _ _ le1 _ st)
        (values h2 hp2 (le-trans _ _ _ le1 le2) $ Cons _ (addr-weaken _ _ le2 $ vals-one _ vs1) vs))))

  (many eval-picked : (subterm many (Nat) fuel) (erased (Nat) hs) (many (Heap Block hs) hp) (erased (List $ List $ Bin) ctx) (subterm many (List $ Code ctx many-one) cs) (subterm many (List $ Mult) ms) (erased (Picked (Code ctx many-one) ms cs) pk) (many (St hs ctx) st) ->
      (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Vals hs2 ms) vs)
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
                    (let (erased h2) (many hp2) (erased le2) (many vs) $ eval-picked fuel _ hp1 _ crest rest p $ st-weaken _ _ le1 _ st)
                    (values h2 hp2 (le-trans _ _ _ le1 le2) $ ValsMany _ _ (addr-weaken _ _ le2 $ vals-one _ vs1) vs))))))
          ((Erased)
            (match erased pk _
              ((PkErased ta ms2 cs2 p)
                (let (erased h2) (many hp2) (erased le2) (many vs) $ eval-picked fuel _ hp _ cs rest p st)
                (values h2 hp2 le2 $ ValsErased _ _ vs))))))))

  (many eval-branch : (subterm many (Nat) fuel) (erased (Nat) hs) (many (Heap Block hs) hp) (erased (List $ List $ Bin) ctx) (many (List $ Mult) ns) (subterm many (List $ Branch ctx ns) bs) (many (Nat) i) (many (List $ Addr hs) fields) (many (St hs ctx) st) ->
      (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Vals hs2 ns) vs)
    (match many bs _
      ((Nil a) (error-vals _ hp ns $ str-cat "no branch for discriminant " $ nat-str i))
      ((Cons a b rest)
        (match many b _
          ((MkBranch c n0 d ids body)
            (match many (nat-cmp d i) _
              ((CEq eq-t eq-r eq-x)
                (let (erased h1) (many hp1) (erased le1) (many fs) (erased lk) $ fit-addrs _ hp ids fields)
                (let (erased h2) (many hp2) (erased le2) (many r) $ eval fuel _ hp1 _ _ body $ st-push _ _ (st-weaken _ _ le1 _ st) ids fs lk)
                (values h2 hp2 (le-trans _ _ _ le1 le2) r))
              (else (eval-branch fuel _ hp _ ns rest i fields st))))))))

  ; A closure is a member of the group at its block: the body runs over the parameters, the group's frame
  ; and the frames the group closed over. A missing member is an error block (ASSUMPTIONS 127).
  (many apply : (subterm many (Nat) fuel) (erased (Nat) hs) (many (Heap Block hs) hp) (many (IdMap $ EInfo hs) cs) (many (Addr hs) f) (many (List $ Addr hs) args) ->
      (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (List $ Addr hs2) vs)
    (let (erased fa) (erased flt) (many fb) $ deref Block _ hp f)
    (match many fb _
      ((BFn z ga i id)
        (let (many g) $ addr-weaken _ _ (lt-weaken _ _ flt) ga)
        (let (erased gn) (erased glt) (many gb) $ deref Block _ hp g)
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
                            (let (erased (Nat) h1) (many (Heap Block h1) hp1) (erased (Lt hs (Succ h1)) le1) (many (Maybe $ List $ Addr h1) done)
                              (match many impl _
                                ((None a) (values hs hp (le-refl hs) $ None _))
                                ((Some a se)
                                  (match many se _
                                    ((MkSomeExtern n e)
                                      (let (many hp2) (many r) $ apply-extern _ e _ hp args)
                                      (let (many (Maybe $ List $ Addr (Succ hs)) r2) $ match many r _ ((Some t v) (Some _ $ Cons _ v $ Nil _)) ((None t) (None _)))
                                      (values (Succ hs) hp2 (le-step _ _ $ le-refl hs) r2))))))
                            (match many done _
                              ((Some a r) (values h1 hp1 le1 r))
                              ((None a)
                                (match many fuel _
                                  ((Zero)
                                    (let (erased h3) (many hp3) (erased le3) (many r) $ error-list _ hp1 "out of fuel")
                                    (values h3 hp3 (le-trans _ _ _ le1 le3) r))
                                  ((Succ k)
                                    (let (erased h2) (many hp2) (erased le2) (many vs) (erased lkp) $ fit-addrs _ hp1 params $ addrs-weaken _ _ le1 args)
                                    (let (erased le12) (le-trans _ _ _ le1 le2))
                                    (let (many env) $ FrVals _ _ params vs lkp $ FrGroup _ _ ids (addr-weaken _ _ le12 g) $ frames-weaken _ _ (le-trans _ _ _ (lt-weaken _ _ glt) le12) _ cenv)
                                    (let (erased h3) (many hp3) (erased le3) (many r) $ eval k _ hp2 _ _ body $ MkSt _ _ (entries-weaken _ _ le12 cs) env)
                                    (values h3 hp3 (le-trans _ _ _ le12 le3) $ vals-list _ _ r))))))))))))))
          (else (error-list _ hp "not a group"))))
      ((BCtorFn z c)
        (let (erased h2) (many hp2) (erased le2) (many v) $ construct _ hp c args)
        (values h2 hp2 le2 $ Cons _ v $ Nil _))
      ((BError z m) (error-list _ hp m))
      (else (error-list _ hp "cannot apply a value that is not a function")))))

(let (many eval-fuel) 1000000)

(def-fns _ $ many run-code : (erased (Nat) hs) (many (Heap Block hs) hp) (many (IdMap $ EInfo hs) cs) (erased (List $ Mult) ms) (many (Code (Nil (List (Bin))) ms) code) -> (erased (Nat) hs2) (many (Heap Block hs2) hp2) (erased (Lt hs (Succ hs2)) le) (many (Vals hs2 ms) vs)
  (eval eval-fuel _ hp _ _ code $ MkSt _ _ cs $ FrNil _))

; ---- Run-position statements against the environment (section 34): each reads the store out, runs or
; allocates, and puts it back with what holds its addresses widened.

(def-fns _ $ many set-states : (erased (Nat) hs) (many (IdMap $ EInfo hs) en) (subterm many (List $ Bin) ids) (many (List $ Addr hs) vs) (erased (Lockstep (Bin) (Addr hs) ids vs) lk) -> (many (IdMap $ EInfo hs) r)
  (match many ids _
    ((Nil a) en)
    ((Cons a x rest)
      (match erased lk _
        ((LsCons ta tb x0 v0 xs vrest0 p)
          (match many vs _
            ((Cons b v vrest) (set-states _ (entries-set-state _ en x $ SConst _ v) rest vrest p))))))))

(def-fns _ $ many env-run-final : (many (Env) e) (many (Code (Nil (List (Bin))) many-one) code) (many (Term) ty) -> (many (Env) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (let (erased hs2) (many hp2) (erased le) (many vs) $ run-code _ hp en _ code)
  (let (many en2) (many fi2) $ store-grow _ _ le en fi)
  (env-with-store e _ hp2 en2 $ Cons _ (MkPair _ _ (vals-one _ vs) ty) fi2))

(def-fns _ $ many close-members : (many (Env) e) (erased (Nat) hs) (many (Heap Block hs) hp) (many (IdMap $ EInfo hs) en) (many (List $ Pair (Addr hs) $ Term) fi) (subterm many (List $ Bin) ids) (many (Addr hs) g) (many (Nat) i) -> (many (Env) r)
  (match many ids _
    ((Nil a) (env-with-store e _ hp en fi))
    ((Cons a x rest)
      (let (many hp2) (many v) $ alloc Block _ hp $ BFn _ g i x)
      (let (erased le) (le-step _ _ $ le-refl hs))
      (let (many en2) (many fi2) $ store-grow _ _ le en fi)
      (close-members e _ hp2 (entries-set-state _ en2 x $ SConst _ v) fi2 rest (addr-weaken _ _ le g) $ Succ i))))

; A run-position def-fns: the group's block over no frames, then a closure block per member.
(def-fns _ $ many env-close-group : (many (Env) e) (erased (List $ Bin) gids) (many (Group gids (Nil (List (Bin)))) g) -> (many (Env) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (let (many hp1) (many ga) $ alloc Block _ hp $ BGroup _ _ _ g $ FrNil _)
  (let (many en1) (many fi1) $ store-grow _ _ (le-step _ _ $ le-refl hs) en fi)
  (match many g _ ((MkGroup c ids fns lk) (close-members e _ hp1 en1 fi1 ids ga 0))))

; The Const fields of a value bound to their ids at their declared multiplicities (section 15): a many
; field its address, an erased one the token, a missing one an error block.
(def-fns _ $ many set-field-states : (erased (Nat) hs) (many (Heap Block hs) hp) (many (IdMap $ EInfo hs) en) (many (List $ Pair (Addr hs) $ Term) fi) (subterm many (List $ Bin) fids) (many (List $ Mult) mults) (many (List $ Addr hs) vs) ->
    (erased (Nat) hs2) (many (Heap Block hs2) hp2) (many (IdMap $ EInfo hs2) en2) (many (List $ Pair (Addr hs2) $ Term) fi2)
  (match many fids _
    ((Nil a) (values hs hp en fi))
    ((Cons a x rest)
      (let (many (Mult) m) (many (List $ Mult) mrest) $ match many mults _ ((Nil b) (values (Many) $ Nil _)) ((Cons b m0 mr) (values m0 mr)))
      (let (many (Block hs) filler) $ match many m _ ((Many) (BError _ "missing value")) ((Erased) (BToken _)))
      (let (many (Maybe $ Addr hs) have) $ match many m _ ((Erased) (None _)) ((Many) (match many vs (((Maybe $ Addr hs) r)) ((Nil b) (None _)) ((Cons b v vrest) (Some _ v)))))
      (let (many (List $ Addr hs) vrest) $ match many m _ ((Erased) vs) ((Many) (match many vs (((List $ Addr hs) r)) ((Nil b) (Nil _)) ((Cons b v vr) vr))))
      (match many have _
        ((Some b v) (set-field-states _ hp (entries-set-state _ en x $ SConst _ v) fi rest mrest vrest))
        ((None b)
          (let (many hp2) (many t) $ alloc Block _ hp filler)
          (let (erased le) (le-step _ _ $ le-refl hs))
          (let (many en2) (many fi2) $ store-grow _ _ le en fi)
          (set-field-states _ hp2 (entries-set-state _ en2 x $ SConst _ t) fi2 rest mrest $ addrs-weaken _ _ le vrest))))))

(def-fns _ $ many env-run-let : (many (Env) e) (many (List $ Mult) ms) (many (Code (Nil (List (Bin))) ms) code) (many (List $ Bin) ids) -> (many (Env) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (let (erased hs2) (many hp2) (erased le) (many vs) $ run-code _ hp en _ code)
  (let (many en2) (many fi2) $ store-grow _ _ le en fi)
  (let (erased hs3) (many hp3) (many en3) (many fi3) $ set-field-states _ hp2 en2 fi2 ids ms $ vals-list _ _ vs)
  (env-with-store e _ hp3 en3 fi3))

; The discriminant of a Const entry's value under a constructor's reading, or None where it is no Const.
(def-fns _ $ many env-destruct : (many (Env) e) (many (Bin) x) (many (Ctor) ct) -> (many (Env) r) (many (Maybe $ Nat) i)
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

(def-fns _ $ many env-set-fields : (many (Env) e) (many (Bin) x) (many (Ctor) ct) (many (List $ Bin) fids) (many (List $ Mult) mults) -> (many (Env) r)
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
(def-fns _ $ many env-run-fields : (many (Env) e) (many (Code (Nil (List (Bin))) many-one) code) (many (Ctor) ct) (many (List $ Bin) fids) (many (List $ Mult) mults) -> (many (Env) r)
  (let (erased hs) (many hp) (many en) (many fi) $ env-store e)
  (let (erased hs1) (many hp1) (erased le1) (many vs) $ run-code _ hp en _ code)
  (let (erased hs2) (many hp2) (erased le2) (many i) (many fs) $ destruct _ hp1 ct $ vals-one _ vs)
  (let (many en2) (many fi2) $ store-grow _ _ (le-trans _ _ _ le1 le2) en fi)
  (let (erased hs3) (many hp3) (many en3) (many fi3) $ set-field-states _ hp2 en2 fi2 fids mults fs)
  (env-with-store e _ hp3 en3 fi3))

; Every binder of a run-position statement that did not run holds the token, as after an error.
(def-fns _ $ many env-set-tokens : (many (Env) e) (subterm many (List $ Bin) ids) -> (many (Env) r)
  (match many ids _
    ((Nil a) e)
    ((Cons a x rest) (env-set-tokens (set-state-closed e x $ BToken _) rest))))
