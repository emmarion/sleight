(def-fns _ $ (many nat-raw : (unique (MacroWorld) mw) (many (Pos) p) (many (Nat) n) -> (unique (MacroWorld) mw2 at mw) (many (Raw) r))
  (let ((unique mw1) (many h)) (intern-nat mw n))
  (values mw1 (RawSettled p _ _ _ h)))

(def-fns _ $ (many str-raw : (unique (MacroWorld) mw) (many (Pos) p) (many (String) s) -> (unique (MacroWorld) mw2 at mw) (many (Raw) r))
  (let ((unique mw1) (many h)) (intern-string mw s))
  (values mw1 (RawSettled p _ _ _ h)))

(def-fns _ $ (many arg-value : (unique (MacroWorld) mw) (many (Raw) r) (erased Type T) (many (Settled (MErased) Type T) th) ->
    (unique (MacroWorld) mw2 at mw) (many (Maybe T) v))
  (let-match many r (RawSettled _ _ _ _ c) (else (values mw (None _))))
  (let-match many (settled-mult _ _ _ c) (MMany) (else (values mw (None _))))
  (let ((unique mw1) (many e)) (settled-eq _ _ _ _ _ _ mw (settled-type _ _ _ c) th))
  (let-match many e (Some _ j) ((None _) (values mw1 (None _))))
  (let-match erased j (JMRefl _ _))
  (values mw1 (Some _ $ settled-value _ _ c)))

(let ((erased nat-type)) (Nat))

(def-fns _ $ (many arg-nat : (unique (MacroWorld) mw) (many (Raw) r) -> (unique (MacroWorld) mw2 at mw) (many (Maybe (Nat)) n))
  (arg-value mw r _ (settled-of erased nat-type)))

(let ((erased arg-string-type)) (String))

(def-fns _ $ (many arg-string : (unique (MacroWorld) mw) (many (Raw) r) -> (unique (MacroWorld) mw2 at mw) (many (Maybe (String)) s))
  (arg-value mw r _ (settled-of erased arg-string-type)))

(def-fns _ $ (many fail-raw : (unique (MacroWorld) mw) (many (Pos) p) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Raw) r))
  (let ((unique mw1) (many m)) (str-raw mw p s))
  (values mw1 $ RawList p $ Cons _ (RawSettled p _ _ _ (settled-of many compile-error)) $ Cons _ m $ Nil _))

(def-fns _ $ (many macro-fail : (unique (MacroWorld) mw) (many (Pos) p) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many r)) (fail-raw mw p s))
  (values mw1 $ Cons _ r $ Nil _))

(def-fns _ $ (many same-sym : (many (Raw) a) (many (Raw) b) -> (many (Bool) r))
  (let-match many a (RawSymbol _ x) (else (BFalse)))
  (let-match many b (RawSymbol _ y) (else (BFalse)))
  (match many (symbol-eq x y) _ ((Some _ _) (BTrue)) ((None _) (BFalse))))

(def-fns _
  ((many same-raw : (subterm many (Raw) a) (many (Raw) b) -> (many (Bool) r))
    (let-match many a (RawList _ xs) ((RawSymbol _ _) (same-sym a b)) (else (BFalse)))
    (let-match many b (RawList _ ys) (else (BFalse)))
    (tail $ same-raws xs ys))
  ((many same-raws : (subterm many (List $ Raw) xs) (many (List $ Raw) ys) -> (many (Bool) r))
    (match many xs _
      ((Nil _) (match many ys _ ((Nil _) (BTrue)) (else (BFalse))))
      ((Cons _ x xr)
        (let-match many ys (Cons _ y yr) ((Nil _) (BFalse)))
        (let-match many (notail $ same-raw x y) (BTrue) ((BFalse) (BFalse)))
        (tail $ same-raws xr yr)))))

(def-fns _ $ (many unquote-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (macro-fail mw here "`~` stands only in a `qq` template"))
(let ((many ~)) (MkMacro _ unquote-fn))

(def-fns _ $ (many unquote-splicing-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (macro-fail mw here "`~@` stands only in a `qq` template"))
(let ((many ~@)) (MkMacro _ unquote-splicing-fn))

(def-fns _ $ (many raws-append : (subterm many (List $ Raw) xs) (many (List $ Raw) ys) -> (many (List $ Raw) r))
  (match many xs _
    ((Nil _) ys)
    ((Cons _ x rest) (Cons _ x $ notail $ raws-append rest ys))))

(def-adts $ (QqPart : -> Type)
  enum
  (many QqPlain : -> (QqPart))
  (many QqOne : (many (Raw) e) -> (QqPart))
  (many QqSplice : (many (Raw) e) -> (QqPart)))

(def-fns _ $ (many qq-part : (unique (MacroWorld) mw) (many (Raw) item) -> (unique (MacroWorld) mw2 at mw) (many (QqPart) r))
  (let-match many item (RawList _ xs) (else (values mw (QqPlain))))
  (let-match many xs (Cons _ h r1) ((Nil _) (values mw (QqPlain))))
  (let-match many r1 (Cons _ e r2) ((Nil _) (values mw (QqPlain))))
  (let-match many r2 (Nil _) ((Cons _ _ _) (values mw (QqPlain))))
  (let-match many h (RawSymbol _ s) (else (values mw (QqPlain))))
  (let ((unique mw1) (many res)) (resolve mw s))
  (let-match many res (RSettled _ _ _ c) (else (values mw1 (QqPlain))))
  (let ((unique mw2) (many single)) (settled-eq _ _ _ _ _ _ mw1 c (settled-of many ~)))
  (let-match many single (None _) ((Some _ _) (values mw2 (QqOne e))))
  (let ((unique mw3) (many spliced)) (settled-eq _ _ _ _ _ _ mw2 c (settled-of many ~@)))
  (match many spliced _ ((Some _ _) (values mw3 (QqSplice e))) ((None _) (values mw3 (QqPlain)))))

(def-fns _ $ (many qq-h : (many (Pos) p) (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) h) -> (many (Raw) r))
  (RawSettled p _ _ _ h))

(def-fns _ $ (many qq-call : (many (Pos) p) (many (Raw) f) (many (List $ Raw) xs) -> (many (Raw) r))
  (RawList p $ Cons _ f xs))

(let ((erased qq-pos-type)) (Pos))

(def-fns _ $ (many qq-pos : (unique (MacroWorld) mw) (many (Pos) here) (many (Raw) r) -> (unique (MacroWorld) mw2 at mw) (many (Raw) code))
  (let ((many p)) $ match many r (((Pos) _)) ((RawSymbol q _) q) ((RawWild q) q) ((RawList q _) q) ((RawSettled q _ _ _ _) q))
  (let ((unique mw1) (many h)) (mint-settled mw _ (settled-of erased qq-pos-type) p))
  (values mw1 (RawSettled here _ _ _ h)))

(def-fns _ $ (many qq-ref : (many (Pos) here) (many (Raw) pr) (erased (Mult) m) (erased Type T) (erased T t) (many (Settled m T t) c) -> (many (Raw) r))
  (let ((many tok)) $ match many (settled-mult _ _ _ c) (((Raw) _))
    ((MErased) (qq-h here _ _ _ (settled-of many erased)))
    ((MMany) (qq-h here _ _ _ (settled-of many many)))
    ((MUnique) (qq-h here _ _ _ (settled-of many unique))))
  (qq-call here (qq-h here _ _ _ (settled-of many RawSettled)) $ Cons _ pr $ Cons _ (RawWild here) $ Cons _ (RawWild here) $ Cons _ (RawWild here)
    $ Cons _ (qq-call here (qq-h here _ _ _ (settled-of many settled-of)) $ Cons _ tok $ Cons _ (RawSettled here _ _ _ c) $ Nil _) $ Nil _))

(def-fns _
  ((many qq-code : (unique (MacroWorld) mw) (many (Pos) here) (subterm many (Raw) t) -> (unique (MacroWorld) mw2 at mw) (many (Raw) code))
    (let ((unique mw1) (many pr)) (qq-pos mw here t))
    (match many t (((MacroWorld) w at mw) ((Raw) _))
      ((RawWild _) (values mw1 $ qq-call here (qq-h here _ _ _ (settled-of many RawWild)) $ Cons _ pr $ Nil _))
      ((RawSettled _ _ _ _ c) (values mw1 $ qq-ref here pr _ _ _ c))
      ((RawSymbol p s)
        (let ((unique mw2) (many res)) (resolve mw1 s))
        (match many res (((MacroWorld) w at mw) ((Raw) _))
          ((RSettled _ _ _ c) (values mw2 $ qq-ref here pr _ _ _ c))
          ((RHypothetical) (fail-raw mw2 p "a local name in a `qq` template; write it `(~ x)`"))
          ((RUnbound) (fail-raw mw2 p "an unbound name in a `qq` template"))))
      ((RawList _ xs)
        (let ((unique mw2) (many items)) (notail $ qq-codes mw1 here xs))
        (values mw2 $ qq-call here (qq-h here _ _ _ (settled-of many RawList)) $ Cons _ pr $ Cons _ items $ Nil _))))
  ((many qq-codes : (unique (MacroWorld) mw) (many (Pos) here) (subterm many (List $ Raw) ts) -> (unique (MacroWorld) mw2 at mw) (many (Raw) code))
    (let-match many ts (Cons _ t rest) ((Nil _) (values mw $ qq-call here (qq-h here _ _ _ (settled-of many Nil)) $ Cons _ (RawWild here) $ Nil _)))
    (let ((unique mw1) (many after)) (notail $ qq-codes mw here rest))
    (let ((unique mw2) (many part)) (qq-part mw1 t))
    (let-match many part (QqPlain)
      ((QqOne e) (values mw2 $ qq-call here (qq-h here _ _ _ (settled-of many Cons)) $ Cons _ (RawWild here) $ Cons _ e $ Cons _ after $ Nil _))
      ((QqSplice e) (values mw2 $ qq-call here (qq-h here _ _ _ (settled-of many raws-append)) $ Cons _ e $ Cons _ after $ Nil _)))
    (let ((unique mw3) (many c)) (notail $ qq-code mw2 here t))
    (values mw3 $ qq-call here (qq-h here _ _ _ (settled-of many Cons)) $ Cons _ (RawWild here) $ Cons _ c $ Cons _ after $ Nil _)))

(def-fns _ $ (many qq-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many code)) (qq-codes mw here args))
  (values mw1 $ Cons _ code $ Nil _))
(let ((many qq)) (MkMacro _ qq-fn))

(def-fns _ $ (many fresh-raw : (unique (MacroWorld) mw) (many (Pos) p) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Raw) r))
  (let ((unique mw1) (many n) (erased g)) (gensym mw s))
  (values mw1 $ RawSymbol p $ SGen n s g))

(def-fns _ $ (many def-macro-shape : (unique (MacroWorld) mw) (many (Pos) here) (many (String) usage)
    (many (Raw) mname) (many (Raw) w) (many (Raw) p) (many (Raw) a) (many (List $ Raw) extra) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) params) (many (List $ Raw) rets) (many (List $ Raw) call))
  (let-match many extra (Cons _ hn r1) ((Nil _) (values mw (Nil _) (Nil _) (qq (values (~ w) $ (~ mname) (~ a))))))
  (let-match many r1 (Cons _ mn r2) ((Nil _) (values mw (qq (many (Pos) (~ hn))) (Nil _) (qq (values (~ w) $ (~ mname) (~ a) (~ p))))))
  (let-match many r2 (Nil _) ((Cons _ _ _) (let ((unique mw1) (many f)) (macro-fail mw here usage)) (values mw1 (Nil _) (Nil _) f)))
  (values mw (qq (many (Pos) (~ hn)) (unique (MacroWorld) (~ mn))) (qq (unique (MacroWorld) _ at (~ mn))) (qq ((~ mname) (~ a) (~ p) (~ w)))))

(def-fns _ $ (many def-macro-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many usage)) "`def-macro` takes a header `(name args [here [mw]])` and a body")
  (let-match many args (Cons _ header body) ((Nil _) (macro-fail mw here usage)))
  (let-match many header (RawList _ hs) (else (macro-fail mw here usage)))
  (let-match many hs (Cons _ mname r1) ((Nil _) (macro-fail mw here usage)))
  (let-match many r1 (Cons _ as extra) ((Nil _) (macro-fail mw here usage)))
  (let ((unique mw1) (many g)) (fresh-raw mw here "macro"))
  (let ((unique mw2) (many w)) (fresh-raw mw1 here "mw"))
  (let ((unique mw3) (many p)) (fresh-raw mw2 here "here"))
  (let ((unique mw4) (many a)) (fresh-raw mw3 here "args"))
  (let ((unique mw5) (many params) (many rets) (many call)) (def-macro-shape mw4 here usage mname w p a extra))
  (values mw5 $ qq
    (let ((many (~ mname)))
      (def-fns _ $ (many (~ mname) : (subterm many (List $ Raw) (~ as)) (~@ params) -> (~@ rets) (many (List $ Raw) _)) (~@ body))
      (def-fns _ $ (many (~ g) : (unique (MacroWorld) (~ w)) (many (Pos) (~ p)) (many (List $ Raw) (~ a)) ->
          (unique (MacroWorld) _ at (~ w)) (many (List $ Raw) _))
        (~@ call))
      (MkMacro _ (~ g)))))
(let ((many def-macro)) (MkMacro _ def-macro-fn))

(def-macro (and args)
  (let-match many args (Cons _ a rest) ((Nil _) (qq (BTrue))))
  (let-match many rest (Cons _ _ _) ((Nil _) args))
  (qq (match many (~ a) (((Bool) _))
        ((BTrue) (~@ $ notail $ and rest))
        ((BFalse) (BFalse)))))

(def-macro (or args)
  (let-match many args (Cons _ a rest) ((Nil _) (qq (BFalse))))
  (let-match many rest (Cons _ _ _) ((Nil _) args))
  (qq (match many (~ a) (((Bool) _))
        ((BTrue) (BTrue))
        ((BFalse) (~@ $ notail $ or rest)))))
