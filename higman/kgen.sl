(def-adts $ (RFrame : -> Type)
  enum
  (many RFr : (many (Bool) dollar) (many (List (Raw)) items) -> (RFrame)))

(def-fns _ $ (many rev-raws : (subterm many (List (Raw)) xs) (many (List (Raw)) acc) -> (many (List (Raw)) ys))
  (let-match many xs (Cons _ x rest) ((Nil _) acc))
  (tail $ rev-raws rest (Cons (Raw) x acc)))

(def-fns _ $ (many chars-rope : (subterm many (List (Char)) rev) (many (Rope) acc) -> (many (Rope) r))
  (let-match many rev (Cons _ c rest) ((Nil _) acc))
  (tail $ chars-rope rest (RCat (RChar c) acc)))

(def-fns _ $ (many chars-str : (many (List (Char)) rev) -> (many (String) s))
  (let ((many s) (erased _)) (flatten (chars-rope rev (REmpty))))
  s)

(def-fns _ $ (many char-code : (many (Char) c) -> (many (Nat) n))
  (let-match many c (MkChar u))
  (let-match many u (MkU8 n _))
  n)

(def-adts $ (Digits : -> Type)
  enum
  (many NotNum : -> (Digits))
  (many Num : (many (Nat) v) -> (Digits)))

(def-fns _ $ (many digits : (subterm many (List (Char)) rev) -> (many (Digits) d))
  (let-match many rev (Cons _ c rest) ((Nil _) (Num (Zero))))
  (let ((many n)) (char-code c))
  (let-match many (lt-dec n 48) (No _ _ _ _ le) ((Yes _ _ _ _ _) (NotNum)))
  (let-match many (lt-dec n 58) (Yes _ _ _ _ _) ((No _ _ _ _ _) (NotNum)))
  (let ((many dv) (erased _)) (sub n 48 (le-lt-succ 48 n le)))
  (let-match many (notail $ digits rest) (Num v) ((NotNum) (NotNum)))
  (Num $ nat-add dv $ nat-mul 10 v))

(def-fns _ $ (many push-item : (many (List (RFrame)) st) (many (Raw) r) -> (many (List (RFrame)) st2))
  (let-match many st (Cons _ f rest) ((Nil _) st))
  (let-match many f (RFr d xs))
  (Cons (RFrame) (RFr d (Cons (Raw) r xs)) rest))

(def-fns _ $ (many atom-raw : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List (Char)) cs) ->
    (unique (MacroWorld) mw2 at mw) (many (Raw) r))
  (let-match many (digits cs) (NotNum) ((Num v) (nat-raw mw here v)))
  (let ((many s)) (chars-str cs))
  (match many (str-eq s "_") (((MacroWorld) w2 at mw) ((Raw) o))
    ((Equal _ _ _) (values mw (RawWild here)))
    ((Unequal _ _ _ _ _) (values mw (RawSymbol here $ SName s)))))

(def-fns _ $ (many flush : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List (Char)) cs) (many (List (RFrame)) st) ->
    (unique (MacroWorld) mw2 at mw) (many (List (RFrame)) st2))
  (let-match many cs (Cons _ _ _) ((Nil _) (values mw st)))
  (let ((unique mw1) (many r)) (atom-raw mw here cs))
  (values mw1 (push-item st r)))

(def-fns _ $ (many close : (many (Pos) here) (subterm many (List (RFrame)) st) (many (List (Raw)) pend) -> (many (List (RFrame)) st2))
  (let-match many st (Cons _ f rest) ((Nil _) st))
  (let-match many f (RFr d xs))
  (let ((many r)) (RawList here $ rev-raws (raws-append pend xs) (Nil (Raw))))
  (match many d _ ((BTrue) (tail $ close here rest (Cons (Raw) r (Nil (Raw))))) ((BFalse) (push-item rest r))))

(def-adts $ (CKind : -> Type)
  enum
  (many KSpace : -> (CKind))
  (many KOpen : -> (CKind))
  (many KClose : -> (CKind))
  (many KDollar : -> (CKind))
  (many KAtom : -> (CKind)))

(def-fns _ $ (many char-kind : (many (Nat) n) -> (many (CKind) k))
  (let-match many (lt-dec n 33) (No _ _ _ _ _) ((Yes _ _ _ _ _) (KSpace)))
  (let-match many (nat-eq n 40) (Unequal _ _ _ _ _) ((Equal _ _ _) (KOpen)))
  (let-match many (nat-eq n 41) (Unequal _ _ _ _ _) ((Equal _ _ _) (KClose)))
  (let-match many (nat-eq n 36) (Unequal _ _ _ _ _) ((Equal _ _ _) (KDollar)))
  (KAtom))

(def-fns _ $ (many read-chars : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (subterm many (String) s) (many (List (Char)) cs)
    (many (List (RFrame)) st) -> (unique (MacroWorld) mw2 at mw) (many (List (Raw)) out))
  (let-match many s (SCons c s1)
    ((SNil)
      (let ((unique mw1) (many st1)) (flush mw here cs st))
      (let-match many st1 (Cons _ f _) ((Nil _) (values mw1 (Nil (Raw)))))
      (let-match many f (RFr _ xs))
      (values mw1 (rev-raws xs (Nil (Raw))))))
  (let ((many kind)) (char-kind (char-code c)))
  (let-match many kind (KAtom) (else (let ((unique mw1) (many st1)) (flush mw here cs st))
    (let ((many st2))
      (match many kind (((List (RFrame)) z))
        ((KOpen) (Cons (RFrame) (RFr (BFalse) (Nil (Raw))) st1))
        ((KClose) (close here st1 (Nil (Raw))))
        ((KDollar) (Cons (RFrame) (RFr (BTrue) (Nil (Raw))) st1))
        (else st1)))
    (tail $ read-chars mw1 here s1 (Nil (Char)) st2)))
  (tail $ read-chars mw here s1 (Cons (Char) c cs) st))

(def-fns _ $ (many read-raws : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (List (Raw)) out))
  (read-chars mw here s (Nil (Char)) (Cons (RFrame) (RFr (BFalse) (Nil (Raw))) (Nil (RFrame)))))


(def-fns _ $ (many cat : (subterm many (List (Rope)) xs) -> (many (Rope) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (REmpty)))
  (RCat x $ notail $ cat rest))

(def-fns _ $ (many names : (many (String) pre) (many (Nat) i) (subterm many (Nat) n) -> (many (List (Rope)) xs))
  (let-match many n (Succ n1) ((Zero) (Nil (Rope))))
  (Cons (Rope) (RCat (RStr pre) (RStr (nat-str i))) $ notail $ names pre (Succ i) n1))

(def-fns _ $ (many spaced : (subterm many (List (Rope)) xs) -> (many (Rope) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (REmpty)))
  (cat $ Cons (Rope) (RStr " ") $ Cons (Rope) x $ Cons (Rope) (notail $ spaced rest) $ Nil (Rope)))

(def-fns _ $ (many rank-params : (subterm many (List (Rope)) xs) -> (many (Rope) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (REmpty)))
  (cat $ Cons (Rope) (RStr " (subterm erased (Nat) ") $ Cons (Rope) x $ Cons (Rope) (RStr ")") $ Cons (Rope) (notail $ rank-params rest) $ Nil (Rope)))

(def-fns _ $ (many rank-term : (subterm many (List (Rope)) xs) -> (many (Rope) r))
  (let-match many xs (Cons _ x rest) ((Nil _) (RStr "(Nil (Nat))")))
  (cat $ Cons (Rope) (RStr "(Cons (Nat) ") $ Cons (Rope) x $ Cons (Rope) (RStr " ") $ Cons (Rope) (notail $ rank-term rest)
    $ Cons (Rope) (RStr ")") $ Nil (Rope)))

; cur : the name of the Length proof still to take apart.
(def-fns _ $ (many destruct : (many (Rope) cur) (subterm many (List (Rope)) xs) -> (many (Rope) r))
  (let-match many xs (Cons _ x rest)
    ((Nil _) (cat $ Cons (Rope) (RStr " (let-match erased ") $ Cons (Rope) cur $ Cons (Rope) (RStr " (LengthNil _))") $ Nil (Rope))))
  (let ((many nxt)) (RCat cur (RStr "x")))
  (cat $ Cons (Rope) (RStr " (let-match erased ") $ Cons (Rope) cur $ Cons (Rope) (RStr " (LengthCons _ ") $ Cons (Rope) x
    $ Cons (Rope) (RStr " _ _ ") $ Cons (Rope) nxt $ Cons (Rope) (RStr "))") $ Cons (Rope) (notail $ destruct nxt rest) $ Nil (Rope)))

; done : the frame's rank arguments before position i, passed unchanged; the call lowers the rank at position i.
(def-fns _ $ (many dispatch : (many (Rope) done) (many (Nat) i) (many (Rope) p lp) (subterm many (List (Rope)) rks) (many (List (Rope)) comps)
    (many (Rope) rest ann) -> (many (Rope) r))
  (let-match many rks (Cons _ rk rks1) ((Nil _) (REmpty)))
  (let-match many comps (Cons _ c comps1) ((Nil _) (REmpty)))
  (let ((many dl)) (RCat (RStr "dl") (RStr (nat-str i))))
  (let ((many ps)) (RCat p (RStr "s")))
  (let ((many lps)) (RCat lp (RStr "s")))
  (let ((many more))
    (match many rks1 (((Rope) o))
      ((Nil _)
        (cat $ Cons (Rope) (RStr "(absurd (Succ ") $ Cons (Rope) ps $ Cons (Rope) (RStr ") (let-match erased ") $ Cons (Rope) lp
          $ Cons (Rope) (RStr " (LPTail _ _ _ _ _ ") $ Cons (Rope) lps $ Cons (Rope) (RStr ")) ") $ Cons (Rope) lps $ Cons (Rope) (RStr ")")
          $ Nil (Rope)))
      ((Cons _ _ _)
        (cat $ Cons (Rope) (RStr "((Succ ") $ Cons (Rope) ps $ Cons (Rope) (RStr ") (let-match erased ") $ Cons (Rope) lp
          $ Cons (Rope) (RStr " (LPTail _ _ _ _ _ ") $ Cons (Rope) lps $ Cons (Rope) (RStr ")) ")
          $ Cons (Rope) (notail $ dispatch (RCat done (RCat (RStr " ") rk)) (Succ i) ps lps rks1 comps1 rest ann) $ Cons (Rope) (RStr ")")
          $ Nil (Rope)))))
  (cat $ Cons (Rope) (RStr "(match many ") $ Cons (Rope) p $ Cons (Rope) (RStr " ") $ Cons (Rope) ann
    $ Cons (Rope) (RStr " ((Zero) (let-match erased ") $ Cons (Rope) lp $ Cons (Rope) (RStr " (LPHead _ _ _ ") $ Cons (Rope) dl
    $ Cons (Rope) (RStr " _ _)) (notail $ frame S R step") $ Cons (Rope) done
    $ Cons (Rope) (RStr " (subterm (lt-subterm ") $ Cons (Rope) c $ Cons (Rope) (RStr " ") $ Cons (Rope) rk $ Cons (Rope) (RStr " ")
    $ Cons (Rope) dl $ Cons (Rope) (RStr ")) ") $ Cons (Rope) c $ Cons (Rope) (spaced comps1) $ Cons (Rope) (RStr " ") $ Cons (Rope) rest
    $ Cons (Rope) (RStr ")) ") $ Cons (Rope) more $ Cons (Rope) (RStr ")") $ Nil (Rope)))

; k : the size of the alphabet; ranks have kn = k+1 entries.
(def-fns _ $ (many dm-text : (many (Nat) k) -> (many (Rope) r))
  (let ((many rk)) (names "rk" 1 (Succ k)))
  (let ((many an)) (names "a" 1 (Succ k)))
  (let ((many bn)) (names "b" 1 (Succ k)))
  (let ((many rp)) (rank-params rk))
  (let ((many rt)) (rank-term rk))
  (let ((many rks)) (spaced rk))
  (let ((many as)) (spaced an))
  (let ((many d1)) (destruct (RStr "ln") an))
  (let ((many d2)) (destruct (RStr "ln2") an))
  (let ((many d3)) (destruct (RStr "ln3") bn))
  (let ((many da)) (dispatch (REmpty) (Zero) (RStr "p") (RStr "lp") rk an (RStr "c2 r2 (Succ q) m t2 x2 d s") (RStr "(((DOut S R kn r2 m) o))")))
  (let ((many dc)) (dispatch (REmpty) (Zero) (RStr "p") (RStr "lp") rk bn (RStr "c3 r3 q m2 t4 x4 ds s2") (RStr "(((DOut S R kn r3 m2) o))")))
  (cat $ Cons (Rope) (RStr "(unary ") $ Cons (Rope) (RStr (nat-str k)) $ Cons (Rope) (RStr ") (let ((many hk)) ") $ Cons (Rope) (RStr (nat-str k))
    $ Cons (Rope) (RStr ") (let ((many kn)) (Succ hk)) ")
    $ Cons (Rope) (RStr "(def-fns _ $ (many dm-factory : (erased (Level) M) ->
    (erased (Level) L)
    (many (Fn L (erased (TyCtor ((List (Grp)) m) -> Type) S) (erased Type R) (many (Fn M (many (List (Grp)) m) (many (S m) s) -> (many (DStep S R kn m) o)) step) (many (List (Grp)) m) (erased (Desc kn m) d) (many (S m) s) -> (many R x)) run))
  (def-fns _ $ (many frame : (erased (TyCtor ((List (Grp)) m) -> Type) S) (erased Type R) (many (Fn M (many (List (Grp)) m) (many (S m) s) -> (many (DStep S R kn m) o)) step)")
    $ Cons (Rope) rp
    $ Cons (Rope) (RStr " (subterm erased (Nat) c)
      (many ")
    $ Cons (Rope) rt
    $ Cons (Rope) (RStr " is r) (many (Nat) q) (many (List (Grp)) m) (erased (List (Grp)) t)
      (erased (Ctx kn r q m (Cons (Grp) (MkGrp r c) t)) x) (erased (Desc kn m) d) (many (S m) s) -> (many (DOut S R kn r m) o))
    (let ((many u0)) (skip q m r kn (Cons (Grp) (MkGrp r c) t) x))
    (let-match many u0 (Cons _ _ t1))
    (let ((erased dt)) (ctx-desc kn q r m (Cons (Grp) (MkGrp r c) t) x d))
    (let-match erased dt (DcCons _ _ _ _ lnr _ hdt dt1))
    (let ((many inner))
    (match many t1 (((DIn S R kn t m) o))
      ((Nil _)
        (match many (step m s) _
          ((DSDone _ _ _ _ z) (DIDone S R kn t m z))
          ((DSNext _ _ _ _ m2 s2 rd dr ds) (DIExit S R kn t m m2 s2 rd (HdNil kn rd) dr ds))))
      ((Cons _ g t2)
        (let-match many g (MkGrp r2 c2))
        (let-match erased dt1 (DcCons _ _ _ _ ln2 _ _ _))
        (let-match erased hdt (HdCons _ _ _ _ _ l2))
        (let-match many (rank-cmp kn r2 r ln2 lnr) (RCLt _ _ _ p lp) (absurd (RCEq _ _) (rlt-irrefl kn r2 l2)) (absurd (RCGt _ _ _ p lp) (rlt-asym kn r2 r l2 (MkRLt kn p r r2 lp))))
        ")
    $ Cons (Rope) d2
    $ Cons (Rope) (RStr "
        (let ((erased x2)) (ctx-next kn q r r2 c c2 m t2 x l2))
        (let ((many o2)) ")
    $ Cons (Rope) da
    $ Cons (Rope) (RStr ")
        (let-match many o2 (DOExit _ _ _ _ _ m3 s3 rd l3 dr ds) ((DODone _ _ _ _ _ z) (DIDone S R kn t m z)))
        (DIExit S R kn t m m3 s3 rd (HdCons kn rd r2 c2 t2 l3) dr ds))))
    (let-match many inner (DIExit _ _ _ _ _ m2 s2 rd h dr ds) ((DIDone _ _ _ _ _ z) (DODone S R kn r m z)))
    (let ((erased lnd)) (drop-length kn rd m m2 dr d))
    (let ((erased sp)) (drop-split kn q c r rd m t m2 x dr h))
    (let-match many (rank-cmp kn r rd lnr lnd) (RCEq _ _)
    ((RCLt _ _ _ p lp) (DOExit S R kn r m m2 s2 rd (MkRLt kn p r rd lp) dr ds))
    (absurd (RCGt _ _ _ p lp)
      (match erased sp _
        (absurd (SpAbove _ _ _ _ _ _ l) (rlt-asym kn r rd l (MkRLt kn p rd r lp)))
        (absurd (SpHere _ _ _ _ _ _ _ _ _) (lexpos-irrefl kn p r lp))
        (absurd (SpGone _ _ _ _ _ _ _ _) (lexpos-irrefl kn p r lp)))))
    (let ((erased t3) (erased x3) (erased sh)) (split-eq kn q c r m2 sp))
    (let ((many u)) (skip q m2 r kn t3 x3))
    (match many u _
    ((Nil _)
      (let-match erased sh (ShGone _ _ _ _ _))
      (let-match many (step m2 s2) (DSNext _ _ _ _ m4 s4 rd2 dr2 ds2) ((DSDone _ _ _ _ z) (DODone S R kn r m z)))
      (let ((erased l4)) (drop-ctx-above kn q r rd2 m2 m4 t3 x3 dr2 (HdNil kn rd2)))
      (DOExit S R kn r m m4 s4 rd2 l4 (drop-compose kn r rd2 m m2 m4 dr dr2 l4) ds2))
    ((Cons _ g3 t4)
      (let-match many g3 (MkGrp r3 c3))
      (let ((erased dt3)) (ctx-desc kn q r m2 t3 x3 ds))
      (let-match erased dt3 (DcCons _ _ _ _ ln3 _ _ _))
      (match many (rank-cmp kn r3 r ln3 lnr) _
        ((RCEq _ _)
          (let-match erased sh (ShHere _ _ _ c4 _ lt)
            (absurd (ShGone _ _ _ _ h5) (let-match erased h5 (HdCons _ _ _ _ _ l5)) (rlt-irrefl kn r l5)))
          (let-match many (notail $ frame S R step")
    $ Cons (Rope) rks
    $ Cons (Rope) (RStr " (subterm (lt-subterm c3 c lt)) c3 r q m2 t4 x3 ds s2)
            (DOExit _ _ _ _ _ m4 s4 rd2 l4 dr2 ds2)
            ((DODone _ _ _ _ _ z) (DODone S R kn r m z)))
          (DOExit S R kn r m m4 s4 rd2 l4 (drop-compose kn r rd2 m m2 m4 dr dr2 l4) ds2))
        ((RCLt _ _ _ p lp)
          (let-match erased sh (ShGone _ _ _ _ h5) (absurd (ShHere _ _ _ _ _ _) (lexpos-irrefl kn p r lp)))
          ")
    $ Cons (Rope) d3
    $ Cons (Rope) (RStr "
          (let ((erased x4)) (ctx-weaken kn q r r3 m2 t3 x3 (MkRLt kn p r3 r lp)))
          (let ((many o4)) ")
    $ Cons (Rope) dc
    $ Cons (Rope) (RStr ")
          (let-match many o4 (DOExit _ _ _ _ _ m4 s4 rd2 l4 dr2 ds2) ((DODone _ _ _ _ _ z) (DODone S R kn r m z)))
          (let ((erased l5)) (drop-ctx-above kn q r rd2 m2 m4 t3 x3 dr2 (HdCons kn rd2 r3 c3 t4 l4)))
          (DOExit S R kn r m m4 s4 rd2 l5 (drop-compose kn r rd2 m m2 m4 dr dr2 l5) ds2))
        (absurd (RCGt _ _ _ p lp)
          (match erased sh _
            (absurd (ShHere _ _ _ _ _ _) (lexpos-irrefl kn p r lp))
            (absurd (ShGone _ _ _ _ h5) (let-match erased h5 (HdCons _ _ _ _ _ l5)) (rlt-asym kn r r3 (MkRLt kn p r r3 lp) l5))))))))
  (def-fns _ $ (many run : (erased (TyCtor ((List (Grp)) m) -> Type) S) (erased Type R) (many (Fn M (many (List (Grp)) m) (many (S m) s) -> (many (DStep S R kn m) o)) step) (many (List (Grp)) m) (erased (Desc kn m) d) (many (S m) s) -> (many R x))
    (match many m _
      ((Nil _)
        (let-match many (step m s) (DSDone _ _ _ _ z) (absurd (DSNext _ _ _ _ _ _ _ dr _) (match erased dr _)))
        z)
      ((Cons _ g t)
        (let-match many g (MkGrp r c))
        (let-match erased d (DcCons _ _ _ _ ln _ _ _))
        ")
    $ Cons (Rope) d1
    $ Cons (Rope) (RStr "
        (let-match many (frame S R step")
    $ Cons (Rope) as
    $ Cons (Rope) (RStr " c r (Zero) m t (CtxHere kn r m) d s) (DODone _ _ _ _ _ z)
          (absurd (DOExit _ _ _ _ _ m2 _ rd l dr _) (drop-top kn r rd c t m2 dr l)))
        z)))
  (values (level-of run) run))")
    $ Nil (Rope)))

(def-macro (def-higman args here mw)
  (let-match many args (Cons _ a _) ((Nil _) (macro-fail mw here "`def-higman` takes one number")))
  (let ((unique mw1) (many v)) (arg-nat mw a))
  (let-match many v (Some _ k) ((None _) (macro-fail mw1 here "`def-higman` takes a constant")))
  (let ((many text) (erased _)) (flatten (dm-text k)))
  (read-raws mw1 here text))
