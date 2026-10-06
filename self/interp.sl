; self/interp.sl -- the compiler's --interpret mode: a program's final values performed by slc itself in
; place of being written out as OCaml (lib/program.ml's consume). A final IO value is walked one request at
; a time: each becomes the same request of slc's own driver, whose continuation puts the answer into the
; compile-time store, applies the program's continuation with self/eval.sl's apply, and walks on; a plain
; value, a thunk's result and a String -> String function's output are printed through the compile-time
; printer. The interpreted program's arguments follow a "--" among slc's own.

; ---- The store as it grows: what is held at an older history, widened to the current one.

(def-fns _ $ (many widen-ref : (erased (Hist Block) a) (erased (Hist Block) b) (erased (Suffix Block b a) le) (many (Ref Block a) r) -> (many (Ref Block b) r2))
  (let ((erased r2) (erased p)) (ref-widen _ _ _ le r))
  (coerce r p))

(def-fns _ $ (many widen-refs : (erased (Hist Block) a) (erased (Hist Block) b) (erased (Suffix Block b a) le) (many (List $ Ref Block a) rs) -> (many (List $ Ref Block b) rs2))
  (let ((erased rs2) (erased p)) (refs-widen _ _ _ le rs))
  (coerce rs p))

(def-fns _ $ (many widen-en : (erased (Hist Block) a) (erased (Hist Block) b) (erased (Suffix Block b a) le) (many (IdMap $ EInfo a) en) -> (many (IdMap $ EInfo b) en2))
  (let ((many en2) (many fi2)) (store-grow _ _ le en (Nil _)))
  en2)

; ---- The prelude's constructors the answers are built from, found as the driver finds them (self/emit.sl).

(def-fns _ $ (many pctor : (many (Env) env) (many (String) name) -> (many (Ctor) c))
  (match many (prelude-ctor env name) _
    ((Some _ c) c)
    ((None _) (MkCtor name 0 0 0 (BFalse) (None _) (Nil _) (BFalse)))))

(def-fns _ $ (many request-name : (many (Env) env) (many (Nat) i) -> (many (String) s))
  (let-match many (prelude-adt env "IO") (Some _ adt)
    ((None _) ""))
  (match many (list-nth _ (adt-ctors adt) i) _ ((NthHit _ _ _ c _) (ctor-name c)) ((NthMiss _ _ _ _) "")))

(def-fns _ $ (many field-at : (erased (Hist Block) hs) (many (List $ Ref Block hs) fields) (many (Nat) i) (many (Ref Block hs) v) -> (many (Ref Block hs) r))
  (match many (list-nth _ fields i) _ ((NthHit _ _ _ x _) x) ((NthMiss _ _ _ _) v)))

; ---- Answers into the store: each allocation grows the history, and what was allocated before is widened.

(def-fns _ $ (many store-wrap : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ctor) c) (many (Ref Block hs) r) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (construct _ hp c (Cons _ r (Nil _))))

(def-fns _ $ (many store-wrapped-str : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ctor) c) (many (String) s) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let ((erased h1) (many hp1) (erased le1) (many r)) (alloc-ext _ hp (PStr s)))
  (let ((erased h2) (many hp2) (erased le2) (many v)) (store-wrap _ hp1 c r))
  (values h2 hp2 (hist-le-trans _ _ _ le1 le2) v))

(def-fns _ $ (many store-maybe-str : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Maybe $ String) m) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many m _
    ((None _) (construct _ hp (pctor env "None") (Nil _)))
    ((Some _ s) (store-wrapped-str _ hp (pctor env "Some") s))))

(def-fns _ $ (many store-strs : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ String) xs) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many xs (Cons _ x rest) ((Nil _) (construct _ hp (pctor env "Nil") (Nil _))))
  (let ((erased h1) (many hp1) (erased le1) (many tl)) (notail $ store-strs env _ hp rest))
  (let ((erased h2) (many hp2) (erased le2) (many hd)) (alloc-ext _ hp1 (PStr x)))
  (let ((erased h3) (many hp3) (erased le3) (many v)) (construct _ hp2 (pctor env "Cons") (Cons _ hd (Cons _ (widen-ref _ _ le2 tl) (Nil _)))))
  (values h3 hp3 (hist-le-trans _ _ _ (hist-le-trans _ _ _ le1 le2) le3) v))

(def-fns _ $ (many store-pairs : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (subterm many (List $ Pair (String) (String)) xs) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many xs (Cons _ x rest) ((Nil _) (construct _ hp (pctor env "Nil") (Nil _))))
  (let-match many x (MkPair _ _ n s))
  (let ((erased h1) (many hp1) (erased le1) (many tl)) (notail $ store-pairs env _ hp rest))
  (let ((erased h2) (many hp2) (erased le2) (many nr)) (alloc-ext _ hp1 (PStr n)))
  (let ((erased h3) (many hp3) (erased le3) (many sr)) (alloc-ext _ hp2 (PStr s)))
  (let ((erased h4) (many hp4) (erased le4) (many pr)) (construct _ hp3 (pctor env "MkPair") (Cons _ (widen-ref _ _ le3 nr) (Cons _ sr (Nil _)))))
  (let ((erased le14)) (hist-le-trans _ _ _ (hist-le-trans _ _ _ le1 le2) (hist-le-trans _ _ _ le3 le4)))
  (let ((erased h5) (many hp5) (erased le5) (many v)) (construct _ hp4 (pctor env "Cons") (Cons _ pr (Cons _ (widen-ref _ _ (hist-le-trans _ _ _ (hist-le-trans _ _ _ le2 le3) le4) tl) (Nil _)))))
  (values h5 hp5 (hist-le-trans _ _ _ le14 le5) v))

; A Result: Ok over a value already in the store, or Fail over the message.
(def-fns _ $ (many store-ok : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) r) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (store-wrap _ hp (pctor env "Ok") r))

(def-fns _ $ (many store-fail : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (String) m) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (store-wrapped-str _ hp (pctor env "Fail") m))

(def-fns _ $ (many store-result-str : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Result $ String) r) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many r _
    ((Ok _ s) (store-wrapped-str _ hp (pctor env "Ok") s))
    ((Fail _ m) (store-fail env _ hp m))))

(def-fns _ $ (many store-result-nullary : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (String) ctor) (many (Maybe $ String) failed) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many failed (None _) ((Some _ m) (store-fail env _ hp m)))
  (let ((erased h1) (many hp1) (erased le1) (many r)) (construct _ hp (pctor env ctor) (Nil _)))
  (let ((erased h2) (many hp2) (erased le2) (many v)) (store-ok env _ hp1 r))
  (values h2 hp2 (hist-le-trans _ _ _ le1 le2) v))

(def-fns _ $ (many store-result-unit : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Result $ Unit) r) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (store-result-nullary env _ hp "MkUnit" (match many r (((Maybe $ String) _)) ((Ok _ _) (None _)) ((Fail _ m) (Some _ m)))))

(def-fns _ $ (many store-result-kind : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Result $ EntryKind) r) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many r _
    ((Ok _ k) (store-result-nullary env _ hp (match many k (((String) _)) ((IsFile) "IsFile") ((IsDir) "IsDir") ((IsOther) "IsOther") ((Missing) "Missing")) (None _)))
    ((Fail _ m) (store-fail env _ hp m))))

(def-fns _ $ (many store-result-change : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Result $ Change) r) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (match many r _
    ((Ok _ c) (store-result-nullary env _ hp (match many c (((String) _)) ((Changed) "Changed") ((Unchanged) "Unchanged")) (None _)))
    ((Fail _ m) (store-fail env _ hp m))))

(def-fns _ $ (many store-result-strs : (many (Env) env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Result $ List $ String) r) ->
    (erased (Hist Block) hs2) (many (Store Block hs2) hp2) (erased (Suffix Block hs2 hs) le) (many (Ref Block hs2) v))
  (let-match many r (Ok _ xs) ((Fail _ m) (store-fail env _ hp m)))
  (let ((erased h1) (many hp1) (erased le1) (many l)) (store-strs env _ hp xs))
  (let ((erased h2) (many hp2) (erased le2) (many v)) (store-ok env _ hp1 l))
  (values h2 hp2 (hist-le-trans _ _ _ le1 le2) v))

; ---- Reading a value out: a String or a U8's Nat held under the FFI, the printed form of any value, and the
; message of an error block, which the interpreter returns where the reference raises (self/README.md).

(def-fns _ $ (many error-of : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) v) -> (many (Maybe $ String) m))
  (let ((erased ns) (many b) (erased sf)) (store-read Block hs hp v))
  (match many b _ ((BError _ m) (Some _ m)) (else (None _))))

(def-fns _ $ (many final-text : (erased (Hist Block) hs) (many (Store Block hs) hp) (many (Ref Block hs) v) (many (Env) env) (many (Term) ty) -> (many (String) s))
  (let-match many (named-final _ hp v env) (None _) ((Some _ text) text))
  (let ((many body) (many app)) (show-at _ hp v 100000 env ty))
  (rope-str (match many app (((Rope) _)) ((BTrue) (rwrap "(" body ")")) ((BFalse) body))))

(def-fns _ $ (many captured-word : (many (Env) env) (erased (Hist Block) hs) (many (IdMap $ EInfo hs) en) (subterm many (List $ Nat) ids) (many (Term) place) -> (many (Maybe $ Ref Block hs) r))
  (let-match many ids (Cons _ id rest) ((Nil _) (None _)))
  (match many (and (is-const env id) (at-equal env place (TVar id))) _
    ((BTrue) (const-ref _ en id))
    ((BFalse) (tail $ captured-word env _ en rest place))))

; The physical result of a final function, or, where its return is promised at an argument or a captured
; word, that word (lib/program.ml's adapt_final, self/emit.sl's adapt-final-rope).
(def-fns _ $ (many final-ref : (many (Env) env) (erased (Hist Block) hs) (many (IdMap $ EInfo hs) en) (many (List $ Entry) rets) (many (List $ Ref Block hs) vs) (many (Maybe $ Ref Block hs) arg) (many (Ref Block hs) fallback) -> (many (Ref Block hs) r))
  (let-match many vs (Nil _) ((Cons _ v _) v))
  (let ((many (Maybe $ Ref Block hs) held))
    (match many rets _
      ((Nil _) (None _))
      ((Cons _ e _)
        (let-match many (entry-place e) (Some _ slot) ((None _) (None _)))
        (let-match many slot (TSlotHolds place) (else (None _)))
        (let-match many place (TVar id)
          ((TBound _) arg)
          (else (captured-word env _ en (env-words env) place)))
        (match many (const-ref _ en id) _ ((Some _ r) (Some _ r)) ((None _) (captured-word env _ en (env-words env) place))))))
  (match many held _ ((Some _ r) r) ((None _) fallback)))

(def-fns _ $ (many fn-rets : (many (Env) env) (many (Term) ty) -> (many (List $ Entry) rets))
  (match many (canon-env env ty) _ ((TFn _ _ _ rs) rs) (else (Nil _))))

; The program's continuation applied to its answer, which was allocated after the request was read: the
; continuation and the Consts are widened to the answer's history first. A request's continuation is a
; UniqueFn the request owned, so it is applied once, here.
(def-fns _ $ (many applied : (erased (Hist Block) hs) (erased (Hist Block) hs2) (erased (Suffix Block hs2 hs) le) (many (Store Block hs2) hp) (many (IdMap $ EInfo hs) en) (many (Ref Block hs) k) (many (List $ Ref Block hs2) args) ->
    (erased (Hist Block) hs3) (many (Store Block hs3) hp3) (many (IdMap $ EInfo hs3) en3) (many (Ref Block hs3) v))
  (let ((erased h3) (many hp3) (erased le3) (many vs) (erased pk)) (apply eval-fuel _ hp (widen-en _ _ le en) (widen-ref _ _ le k) args many-one))
  (values h3 hp3 (widen-en _ _ le3 (widen-en _ _ le en)) (vals-one _ vs pk)))

(def-adts $ (Request : -> Type)
  enum
  (many RqUnknown : -> (Request))
  (many RqExit : -> (Request)) (many RqStep : -> (Request)) (many RqWriteOut : -> (Request))
  (many RqWriteErr : -> (Request)) (many RqReadLine : -> (Request)) (many RqReadFile : -> (Request))
  (many RqWriteFile : -> (Request)) (many RqGetArgs : -> (Request)) (many RqGetEnv : -> (Request))
  (many RqGetEnvs : -> (Request)) (many RqAppendFile : -> (Request)) (many RqReadRemaining : -> (Request))
  (many RqListDir : -> (Request)) (many RqGetCwd : -> (Request)) (many RqStat : -> (Request))
  (many RqMkDir : -> (Request)) (many RqDeleteFile : -> (Request)) (many RqDeleteDir : -> (Request))
  (many RqConfineDir : -> (Request)) (many RqConfineOutputBytes : -> (Request)))

(def-adts $ (RqEntry : -> Type)
  enum
  (many MkRqEntry : (many (String) name) (many (Request) rq) -> (RqEntry)))

(def-fns _ $ (many rq-cons : (many (String) name) (many (Request) rq) (many (List $ RqEntry) rest) -> (many (List $ RqEntry) r))
  (Cons _ (MkRqEntry name rq) rest))

(let ((many request-table))
  $ rq-cons "Exit" (RqExit) $ rq-cons "Step" (RqStep) $ rq-cons "WriteOut" (RqWriteOut) $
  rq-cons "WriteErr" (RqWriteErr) $ rq-cons "ReadLine" (RqReadLine) $ rq-cons "ReadFile" (RqReadFile) $
  rq-cons "WriteFile" (RqWriteFile) $ rq-cons "GetArgs" (RqGetArgs) $ rq-cons "GetEnv" (RqGetEnv) $
  rq-cons "GetEnvs" (RqGetEnvs) $ rq-cons "AppendFile" (RqAppendFile) $ rq-cons "ReadRemaining" (RqReadRemaining) $
  rq-cons "ListDir" (RqListDir) $ rq-cons "GetCwd" (RqGetCwd) $ rq-cons "Stat" (RqStat) $
  rq-cons "MkDir" (RqMkDir) $ rq-cons "DeleteFile" (RqDeleteFile) $ rq-cons "DeleteDir" (RqDeleteDir) $ rq-cons "ConfineDir" (RqConfineDir) $
  rq-cons "ConfineOutputBytes" (RqConfineOutputBytes) $ Nil _)

(def-fns _ $ (many request-of : (subterm many (List $ RqEntry) es) (many (String) name) -> (many (Request) r))
  (let-match many es (Cons _ e rest) ((Nil _) (RqUnknown)))
  (let-match many e (MkRqEntry n rq))
  (match many (str-eq name n) _
    ((BTrue) rq)
    ((BFalse) (tail $ request-of rest name))))

; ---- The levels of the compiler's own IO program (self/main.sl), and the codes it exits with.

(def-lvl util-lvl)
(def-lvl interp-lvl)
(def-lvl finals-lvl)
(def-lvl run-lvl)
(def-lvl compile-lvl)
(def-lvl slc-lvl)
(def-lvl start-lvl)
(def-lvl io-lvl)

(let ((many zero-below-modulus)) $ lt-dec 0 u8-modulus)
(comptime-match many zero-below-modulus (Yes ok-a ok-b ok-lt))
(let ((many exit-ok)) $ MkU8 0 ok-lt)
(let ((many one-below-modulus)) $ lt-dec 1 u8-modulus)
(comptime-match many one-below-modulus (Yes fail-a fail-b fail-lt))
(let ((many exit-fail)) $ MkU8 1 fail-lt)

(def-fns util-lvl $ (many runtime-error : (many (String) m) -> (unique (IO io-lvl) io))
  (WriteErr _ (str-cat3 "slc: runtime error: " m "\n") (unique-thunk _ _ (Exit _ exit-fail))))

; ---- The IO walk: one request of the program becomes one request of slc, whose continuation resumes it.

(def-fns interp-lvl $ (many interp-io : (many (Env) env) (many (List $ String) pargs) (many (Bool) with-env) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) en) (many (Ref Block hs) v) -> (unique (IO io-lvl) io))
  (let-match many (error-of _ hp v) (None _) ((Some _ m) (runtime-error m)))
  (let ((erased h1) (many hp1) (erased le1) (many i) (many fields)) (destruct _ hp (pctor env "Exit") v))
  (let ((erased le0)) (le-refl h1))
  (let ((many en1)) (widen-en _ _ le1 en))
  (let ((many v1)) (widen-ref _ _ le1 v))
  (let ((many name)) (request-name env i))
  (let ((many f0)) (field-at _ fields 0 v1))
  (let ((many f1)) (field-at _ fields 1 v1))
  (let ((many f2)) (field-at _ fields 2 v1))
  (let ((many s0)) (heap-str _ hp1 f0))
  (let ((many s1)) (heap-str _ hp1 f1))
  (match many (request-of request-table name) _
    ((RqUnknown)
      (WriteErr _ (str-cat3 "slc: cannot interpret the request " name "\n") (unique-thunk _ _ (Exit _ exit-fail))))
    ((RqExit)
      (let ((many n)) (heap-nat _ hp1 f0))
      (match many (lt-dec n u8-modulus) _
        ((Yes _ _ p) (Exit _ (MkU8 n p)))
        ((No _ _ _) (Exit _ exit-fail))))
    ((RqStep)
      (def-unique io-lvl $ (unique k : -> (unique (IO io-lvl) next)) (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le0 hp1 en1 f0 (Nil _)))
        (interp-io env pargs with-env _ hp3 en3 next))
      (Step _ k))
    ((RqWriteOut)
      (def-unique io-lvl $ (unique k : -> (unique (IO io-lvl) next)) (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le0 hp1 en1 f1 (Nil _)))
        (interp-io env pargs with-env _ hp3 en3 next))
      (WriteOut _ s0 k))
    ((RqWriteErr)
      (def-unique io-lvl $ (unique k : -> (unique (IO io-lvl) next)) (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le0 hp1 en1 f1 (Nil _)))
        (interp-io env pargs with-env _ hp3 en3 next))
      (WriteErr _ s0 k))
    ((RqReadLine)
      (def-unique io-lvl $ (unique k : (many (Maybe (String)) line) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-maybe-str env _ hp1 line))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f0 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (ReadLine _ k))
    ((RqReadFile)
      (def-unique io-lvl $ (unique k : (many (Result (String)) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-str env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f1 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (ReadFile _ s0 k))
    ((RqWriteFile)
      (def-unique io-lvl $ (unique k : (many (Result (Unit)) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-unit env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f2 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (WriteFile _ s0 s1 k))
    ((RqGetArgs)
      (def-unique io-lvl $ (unique k : (many (List (String)) args) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-strs env _ hp1 pargs))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f0 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (GetArgs _ k))
    ((RqGetEnv)
      (def-unique io-lvl $ (unique k : (many (Maybe (String)) value) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-maybe-str env _ hp1 $ match many with-env _ ((BTrue) value) ((BFalse) (None _))))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f1 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (GetEnv _ s0 k))
    ((RqGetEnvs)
      (def-unique io-lvl $ (unique k : (many (List (Pair (String) (String))) vars) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-pairs env _ hp1 $ match many with-env _ ((BTrue) vars) ((BFalse) (Nil _))))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f0 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (GetEnvs _ k))
    ((RqAppendFile)
      (def-unique io-lvl $ (unique k : (many (Result (Unit)) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-unit env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f2 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (AppendFile _ s0 s1 k))
    ((RqReadRemaining)
      (def-unique io-lvl $ (unique k : (many (String) rest) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (alloc-ext _ hp1 (PStr rest)))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f0 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (ReadRemaining _ k))
    ((RqListDir)
      (def-unique io-lvl $ (unique k : (many (Result (List (String))) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-strs env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f1 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (ListDir _ s0 k))
    ((RqGetCwd)
      (def-unique io-lvl $ (unique k : (many (String) path) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (alloc-ext _ hp1 (PStr path)))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f0 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (GetCwd _ k))
    ((RqStat)
      (def-unique io-lvl $ (unique k : (many (Result (EntryKind)) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-kind env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f1 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (Stat _ s0 k))
    ((RqMkDir)
      (def-unique io-lvl $ (unique k : (many (Result (Change)) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-change env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f1 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (MkDir _ s0 k))
    ((RqDeleteFile)
      (def-unique io-lvl $ (unique k : (many (Result (Change)) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-change env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f1 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (DeleteFile _ s0 k))
    ((RqDeleteDir)
      (def-unique io-lvl $ (unique k : (many (Result (Change)) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-change env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f1 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (DeleteDir _ s0 k))
    ((RqConfineDir)
      (def-unique io-lvl $ (unique k : (many (Result (Unit)) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-unit env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f1 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (ConfineDir _ s0 k))
    ((RqConfineOutputBytes)
      (def-unique io-lvl $ (unique k : (many (Result (Unit)) r) -> (unique (IO io-lvl) next))
        (let ((erased h2) (many hp2) (erased le2) (many ans)) (store-result-unit env _ hp1 r))
        (let ((erased h3) (many hp3) (many en3) (many next)) (applied _ _ le2 hp2 en1 f1 (Cons _ ans (Nil _))))
        (interp-io env pargs with-env _ hp3 en3 next))
      (ConfineOutputBytes _ (heap-nat _ hp1 f0) k))))

; ---- The finals in order, each as lib/program.ml's consume has it; the finals stay at the history they were
; recorded at and each is widened to the current one as it is reached, so the walk is structural.

(def-fns finals-lvl $ (many interp-finals : (many (Env) env) (many (List $ String) pargs) (many (Bool) with-env) (erased (Hist Block) hs0) (subterm many (List $ Pair (Ref Block hs0) $ Term) fi) (erased (Hist Block) hs) (many (Store Block hs) hp) (many (IdMap $ EInfo hs) en) (erased (Suffix Block hs hs0) le) -> (unique (IO io-lvl) io))
  (let-match many fi (Cons _ f rest) ((Nil _) (Exit _ exit-ok)))
  (let-match many f (MkPair _ _ v0 ty))
  (let ((many v)) (widen-ref _ _ le v0))
  (match many (classify-final env ty) _
    ((FIo) (interp-io env pargs with-env _ hp en v))
    ((FPlain)
      (WriteOut _ (str-cat (final-text _ hp v env ty) "\n") (unique-thunk _ _ (notail $ interp-finals env pargs with-env _ rest _ hp en le))))
    ((FThunk t)
      (let ((many rets)) (fn-rets env ty))
      (let ((erased h1) (many hp1) (erased le1) (many vs) (erased pk)) (apply eval-fuel _ hp en v (Nil _) (physical-mults rets)))
      (let ((many en1)) (widen-en _ _ le1 en))
      (let ((many r)) (final-ref env _ en1 rets vs (None _) (widen-ref _ _ le1 v)))
      (match many (error-of _ hp1 r) _
        ((Some _ m) (runtime-error m))
        ((None _)
          (WriteOut _ (str-cat (final-text _ hp1 r env t) "\n") (unique-thunk _ _ (notail $ interp-finals env pargs with-env _ rest _ hp1 en1 (hist-le-trans _ _ _ le le1)))))))
    ((FMain)
      (def-unique io-lvl $ (unique k : (many (String) input) -> (unique (IO io-lvl) next))
        (let ((many rets)) (fn-rets env ty))
        (let ((erased h1) (many hp1) (erased le1) (many s)) (alloc-ext _ hp (PStr input)))
        (let ((erased h2) (many hp2) (erased le2) (many vs) (erased pk)) (apply eval-fuel _ hp1 (widen-en _ _ le1 en) (widen-ref _ _ le1 v) (Cons _ s (Nil _)) (physical-mults rets)))
        (let ((erased le12)) (hist-le-trans _ _ _ le1 le2))
        (let ((many en2)) (widen-en _ _ le12 en))
        (let ((many r)) (final-ref env _ en2 rets vs (Some _ (widen-ref _ _ le2 s)) (widen-ref _ _ le12 v)))
        (match many (error-of _ hp2 r) _
          ((Some _ m) (runtime-error m))
          ((None _) (WriteOut _ (heap-str _ hp2 r) (unique-thunk _ _ (interp-finals env pargs with-env _ rest _ hp2 en2 (hist-le-trans _ _ _ le le12)))))))
      (ReadRemaining _ k))))
