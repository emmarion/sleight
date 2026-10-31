; One native-compute for many checks. `(native-jobs name ev job ...)` queues jobs and the erased evidence `ev` built from
; their results; `(native-each name xs (x t r) T e pat step nil)` queues one job per element of the Settled list xs and
; folds their evidence; `(native-run)` runs every queued job in one native-compute and binds each name. See PLAN.md's
; native.sl entry. Load after std/macro.sl.

(def-adts $ (NativeQueue : -> Type)
  enum
  (many MkNativeQueue : (many (List $ Raw) binders thunks after) -> (NativeQueue)))

(let ((erased native-queue-type)) (NativeQueue))
(let ((many native-queue-0)) (MkNativeQueue (Nil _) (Nil _) (Nil _)))

(def-fns _ $ (many nq-one : (many (Pos) here) (many (List $ Raw) rs) -> (many (Raw) r))
  (let-match many rs (Cons _ r _) ((Nil _) (RawWild here)))
  r)

(def-fns _ $ (many nq-length : (erased Type A) (subterm many (List A) xs) -> (many (Nat) n))
  (match many xs _ ((Nil _) (Zero)) ((Cons _ _ rest) (Succ $ notail $ nq-length A rest))))

(def-fns _ $ (many nq-lookup : (many (Symbol) s) (subterm many (List $ Pair (Symbol) (Raw)) env) -> (many (Maybe (Raw)) r))
  (let-match many env (Cons _ b rest) ((Nil _) (None _)))
  (let-match many b (MkPair _ _ k v))
  (match many (symbol-eq s k) _ ((Some _ _) (Some _ v)) ((None _) (tail $ nq-lookup s rest))))

(def-fns _
  ((many nq-subst : (many (List $ Pair (Symbol) (Raw)) env) (subterm many (Raw) t) -> (many (Raw) r))
    (let-match many t (RawSymbol _ s) ((RawList p xs) (RawList p $ notail $ nq-substs env xs)) (else t))
    (match many (nq-lookup s env) _ ((Some _ v) v) ((None _) t)))
  ((many nq-substs : (many (List $ Pair (Symbol) (Raw)) env) (subterm many (List $ Raw) ts) -> (many (List $ Raw) r))
    (let-match many ts (Cons _ t rest) ((Nil _) ts))
    (Cons _ (notail $ nq-subst env t) $ notail $ nq-substs env rest)))

(def-fns _
  ((many nq-close : (unique (MacroWorld) mw at vacant-slot) (subterm many (Raw) t) -> (unique (MacroWorld) mw2 at mw) (many (Raw) r))
    (match many t (((MacroWorld) w at mw) ((Raw) _))
      ((RawSymbol p s)
        (let ((unique mw1) (many res)) (resolve mw s))
        (match many res (((MacroWorld) w at mw) ((Raw) _)) ((RSettled _ _ _ c) (values mw1 $ RawSettled p _ _ _ c)) (else (values mw1 t))))
      ((RawList p xs) (let ((unique mw1) (many ys)) (notail $ nq-closes mw xs)) (values mw1 $ RawList p ys))
      (else (values mw t))))
  ((many nq-closes : (unique (MacroWorld) mw at vacant-slot) (subterm many (List $ Raw) ts) -> (unique (MacroWorld) mw2 at mw) (many (List $ Raw) r))
    (let-match many ts (Cons _ t rest) ((Nil _) (values mw ts)))
    (let ((unique mw1) (many u)) (notail $ nq-close mw t))
    (let ((unique mw2) (many us)) (notail $ nq-closes mw1 rest))
    (values mw2 $ Cons _ u us)))

(def-fns _ $ (many nq-binders : (unique (MacroWorld) mw at vacant-slot) (subterm many (List $ Raw) fs) (many (List $ Pair (Symbol) (Raw)) env) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) gs) (many (List $ Pair (Symbol) (Raw)) env2))
  (let-match many fs (Cons _ f rest) ((Nil _) (values mw (Nil _) env)))
  (let ((unique mw1) (many gs) (many env1)) (notail $ nq-binders mw rest env))
  (let-match many f (RawSymbol p s) (else (values mw1 (Cons _ f gs) env1)))
  (let ((unique mw2) (many g)) (fresh-raw mw1 p $ match many s (((String) _)) ((SName x) x) ((SGen _ x _) x)))
  (values mw2 (Cons _ g gs) (Cons _ (MkPair _ _ s g) env1)))

(def-fns _ $ (many nq-pattern : (unique (MacroWorld) mw at vacant-slot) (many (Raw) pat) (many (List $ Pair (Symbol) (Raw)) env) ->
    (unique (MacroWorld) mw2 at mw) (many (Raw) pat2) (many (List $ Pair (Symbol) (Raw)) env2))
  (let-match many pat (RawList p items) (else (values mw pat env)))
  (let-match many items (Cons _ h fs) ((Nil _) (values mw pat env)))
  (let ((unique mw1) (many gs) (many env1)) (nq-binders mw fs env))
  (values mw1 (RawList p $ Cons _ h gs) env1))

(def-fns _ $ (many nq-name : (many (Nat) k) -> (many (Symbol) s)) (SName $ str-append "native-queue-" $ nat-str k))

(def-fns _ $ (many nq-scan : (unique (MacroWorld) mw at vacant-slot) (many (Nat) k) (subterm many (Nat) fuel) (many (Maybe (Raw)) last) ->
    (unique (MacroWorld) mw2 at mw) (many (Nat) next) (many (Maybe (Raw)) found))
  (let ((unique mw1) (many res)) (resolve mw (nq-name k)))
  (let-match many res (RSettled _ _ _ c) (else (values mw1 k last)))
  (let-match many fuel (Succ f) ((Zero) (values mw1 k last)))
  (tail $ nq-scan mw1 (Succ k) f (Some _ (RawSettled (NoPos) _ _ _ c))))

(def-fns _ $ (many nq-read : (unique (MacroWorld) mw at vacant-slot) ->
    (unique (MacroWorld) mw2 at mw) (many (Raw) next) (many (Maybe (NativeQueue)) q))
  (let ((unique mw1) (many k) (many found)) (nq-scan mw 0 1000000 (None _)))
  (let ((many next)) (RawSymbol (NoPos) $ nq-name k))
  (let-match many found (Some _ r) ((None _) (values mw1 next (None _))))
  (let ((unique mw2) (many q)) (arg-value mw1 r _ (settled-of erased native-queue-type)))
  (values mw2 next q))

(def-fns _ $ (many nq-bad : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (String) usage) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) defs binders thunks after))
  (let ((unique mw1) (many m)) (macro-fail mw here usage))
  (values mw1 m (Nil _) (Nil _) (Nil _)))

(def-fns _ $ (many nq-job : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (Raw) job) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) defs binders thunks after))
  (let ((many usage)) "a job is `(f pattern)` or `(T e pattern)`")
  (let-match many job (RawList _ items) (else (nq-bad mw here usage)))
  (let-match many items (Cons _ a r1) ((Nil _) (nq-bad mw here usage)))
  (let-match many r1 (Cons _ b r2) ((Nil _) (nq-bad mw here usage)))
  (let ((unique mw1) (many g)) (fresh-raw mw here "res"))
  (let ((unique mw2) (many j)) (fresh-raw mw1 here "job"))
  (let ((unique mw3) (many f) (many defs) (many pat)) $ match many r2 (((MacroWorld) w at mw2) ((Raw) _) ((List $ Raw) _) ((Raw) _))
    ((Nil _) (let ((unique mw3) (many f)) (nq-close mw2 a)) (values mw3 f (Nil _) b))
    ((Cons _ pat _) (values mw2 j (qq (def-fns _ $ (many (~ j) : -> (many (~ a) _)) (~ b))) pat)))
  (let ((unique mw4) (many pat2)) (nq-close mw3 pat))
  (values mw4 defs (qq (many (~ g))) (Cons _ f (Nil _)) (qq (comptime-match many (~ g) (~ pat2)))))

(def-fns _ $ (many nq-jobs : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (subterm many (List $ Raw) jobs) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) defs binders thunks after))
  (let-match many jobs (Cons _ job rest) ((Nil _) (values mw (Nil _) (Nil _) (Nil _) (Nil _))))
  (let ((unique mw1) (many d1) (many b1) (many t1) (many a1)) (nq-job mw here job))
  (let ((unique mw2) (many d2) (many b2) (many t2) (many a2)) (notail $ nq-jobs mw1 here rest))
  (values mw2 (raws-append d1 d2) (raws-append b1 b2) (raws-append t1 t2) (raws-append a1 a2)))

(def-fns _ $ (many nq-patterns : (unique (MacroWorld) mw at vacant-slot) (subterm many (List $ Raw) jobs) (many (List $ Pair (Symbol) (Raw)) env) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) jobs2) (many (List $ Pair (Symbol) (Raw)) env2))
  (let-match many jobs (Cons _ job rest) ((Nil _) (values mw (Nil _) env)))
  (let ((unique mw1) (many rest2) (many env1)) (notail $ nq-patterns mw rest env))
  (let-match many job (RawList p items) (else (values mw1 (Cons _ job rest2) env1)))
  (let-match many items (Cons _ a r1) ((Nil _) (values mw1 (Cons _ job rest2) env1)))
  (let-match many r1 (Cons _ b r2) ((Nil _) (values mw1 (Cons _ job rest2) env1)))
  (let-match many r2 (Cons _ c _) ((Nil _)
    (let ((unique mw2) (many b2) (many env2)) (nq-pattern mw1 b env1))
    (values mw2 (Cons _ (RawList p $ Cons _ a $ Cons _ b2 $ Nil _) rest2) env2)))
  (let ((unique mw2) (many c2) (many env2)) (nq-pattern mw1 c env1))
  (values mw2 (Cons _ (RawList p $ Cons _ a $ Cons _ b $ Cons _ c2 $ Nil _) rest2) env2))

(def-fns _ $ (many nq-queue : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (Raw) name ev) (many (List $ Raw) jobs) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many next) (many q)) (nq-read mw))
  (let-match many q (Some _ nq) ((None _) (macro-fail mw1 here "no `native-queue-0` in scope: load native.sl")))
  (let-match many nq (MkNativeQueue bs ts as))
  (let ((unique mw2) (many defs) (many b1) (many t1) (many a1)) (nq-jobs mw1 here jobs))
  (let ((unique mw3) (many ev2)) (nq-close mw2 ev))
  (let ((many a2)) (raws-append a1 $ qq (let ((erased (~ name))) (~ ev2))))
  (let ((unique mw4) (many h)) (mint-settled mw3 _ (settled-of erased native-queue-type)
    (MkNativeQueue (raws-append bs b1) (raws-append ts t1) (raws-append as a2))))
  (values mw4 $ raws-append defs $ qq (let ((many (~ next))) (~ (RawSettled here _ _ _ h)))))

(def-macro (native-jobs args here mw)
  (let-match many args (Cons _ name r1) ((Nil _) (macro-fail mw here "`native-jobs` takes a name, its evidence and jobs")))
  (let-match many r1 (Cons _ ev jobs) ((Nil _) (macro-fail mw here "`native-jobs` takes a name, its evidence and jobs")))
  (let ((unique mw1) (many jobs2) (many env)) (nq-patterns mw jobs (Nil _)))
  (nq-queue mw1 here name (nq-subst env ev) jobs2))

(def-fns _ $ (many nq-each : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (subterm many (Nat) n) (many (Raw) xs) (many (Symbol) x t r)
    (many (Raw) ty e pat step nil) -> (unique (MacroWorld) mw2 at mw) (many (List $ Raw) cms jobs) (many (Raw) ev))
  (let-match many n (Succ k) ((Zero) (values mw (qq (comptime-match many (~ xs) (Nil _))) (Nil _) nil)))
  (let ((unique mw1) (many gx)) (fresh-raw mw here "x"))
  (let ((unique mw2) (many gt)) (fresh-raw mw1 here "t"))
  (let ((unique mw3) (many cms) (many jobs) (many ev)) (notail $ nq-each mw2 here k gt x t r ty e pat step nil))
  (let ((many env)) (Cons _ (MkPair _ _ x gx) $ Cons _ (MkPair _ _ t gt) $ Nil _))
  (let ((unique mw4) (many pat2) (many env2)) (nq-pattern mw3 (nq-subst env pat) (Cons _ (MkPair _ _ r ev) env)))
  (values mw4 (raws-append (qq (comptime-match many (~ xs) (Cons _ (~ gx) (~ gt)))) cms)
    (Cons _ (RawList here $ Cons _ (nq-subst env ty) $ Cons _ (nq-subst env e) $ Cons _ pat2 $ Nil _) jobs) (nq-subst env2 step)))

(def-macro (native-each-at args here mw)
  (let ((many usage)) "`native-each` takes a name, a Settled list, `(x t r)`, a result type, a body, a pattern, a step and a nil")
  (let-match many args (Cons _ gn r0) ((Nil _) (macro-fail mw here usage)))
  (let-match many r0 (Cons _ name r1) ((Nil _) (macro-fail mw here usage)))
  (let-match many r1 (Cons _ xs r2) ((Nil _) (macro-fail mw here usage)))
  (let-match many r2 (Cons _ vs r3) ((Nil _) (macro-fail mw here usage)))
  (let-match many r3 (Cons _ ty r4) ((Nil _) (macro-fail mw here usage)))
  (let-match many r4 (Cons _ e r5) ((Nil _) (macro-fail mw here usage)))
  (let-match many r5 (Cons _ pat r6) ((Nil _) (macro-fail mw here usage)))
  (let-match many r6 (Cons _ step r7) ((Nil _) (macro-fail mw here usage)))
  (let-match many r7 (Cons _ nil _) ((Nil _) (macro-fail mw here usage)))
  (let-match many vs (RawList _ v1) (else (macro-fail mw here usage)))
  (let-match many v1 (Cons _ rx v2) ((Nil _) (macro-fail mw here usage)))
  (let-match many v2 (Cons _ rt v3) ((Nil _) (macro-fail mw here usage)))
  (let-match many v3 (Cons _ rr _) ((Nil _) (macro-fail mw here usage)))
  (let-match many rx (RawSymbol _ x) (else (macro-fail mw here usage)))
  (let-match many rt (RawSymbol _ t) (else (macro-fail mw here usage)))
  (let-match many rr (RawSymbol _ r) (else (macro-fail mw here usage)))
  (let-match many gn (RawSymbol _ sn) (else (macro-fail mw here usage)))
  (let ((unique mw1) (many res)) (resolve mw sn))
  (let-match many res (RSettled _ _ _ c) (else (macro-fail mw1 here usage)))
  (let ((unique mw2) (many mn)) (arg-nat mw1 (RawSettled here _ _ _ c)))
  (let-match many mn (Some _ n) ((None _) (macro-fail mw2 here usage)))
  (let ((unique mw3) (many cms) (many jobs) (many ev)) (nq-each mw2 here n xs x t r ty e pat step nil))
  (let ((unique mw4) (many out)) (nq-queue mw3 here name ev jobs))
  (values mw4 $ raws-append cms out))

(def-macro (native-each args here mw)
  (let-match many args (Cons _ name r1) ((Nil _) (macro-fail mw here "`native-each` takes a name and a Settled list first")))
  (let-match many r1 (Cons _ xs _) ((Nil _) (macro-fail mw here "`native-each` takes a name and a Settled list first")))
  (let ((unique mw1) (many n)) (fresh-raw mw here "n"))
  (values mw1 $ qq (let ((many (~ n))) (nq-length _ (~ xs))) (native-each-at (~ n) (~@ args))))

(def-macro (native-run args here mw)
  (let ((unique mw1) (many next) (many q)) (nq-read mw))
  (let-match many q (Some _ nq) ((None _) (macro-fail mw1 here "no `native-queue-0` in scope: load native.sl")))
  (let-match many nq (MkNativeQueue bs ts as))
  (let ((many run)) $ match many ts (((List $ Raw) _)) ((Nil _) (Nil _)) (else (qq (let ((~@ bs)) (native-compute (~@ ts))))))
  (values mw1 $ raws-append run $ raws-append as $
    qq (let ((many (~ next))) (MkNativeQueue (Nil _) (Nil _) (Nil _)))))
