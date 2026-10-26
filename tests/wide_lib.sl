; needs: ../std/macro
; `(wide kind T P n k F)` writes n items named P0 to P(n-1); item i has 1 + (i mod k) fields of type F, or
; none when k is 0:
; kind `ctors`, the constructors of T; `params`, erased ValCtor parameters; `matchable`, the one type
; `(Matchable enum T (many P0) ...)`; `names`, the bare names.
(def-adts $ (WideKind : -> Type)
  enum
  (many WkCtors : -> (WideKind))
  (many WkParams : -> (WideKind))
  (many WkMatchable : -> (WideKind))
  (many WkNames : -> (WideKind)))

(def-fns _ $ (many sym-text : (many (Raw) r) -> (many (String) s))
  (let-match many r (RawSymbol _ y) (else ""))
  (let-match many y (SName s) (else ""))
  s)

(def-fns _ $ (many is-text : (many (String) s) (many (String) t) -> (many (Bool) r))
  (match many (str-cmp s t) _ ((CEq _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many kind-of : (many (String) s) -> (many (Maybe $ WideKind) k))
  (let-match many (is-text s "ctors") (BFalse) ((BTrue) (Some _ $ WkCtors)))
  (let-match many (is-text s "params") (BFalse) ((BTrue) (Some _ $ WkParams)))
  (let-match many (is-text s "matchable") (BFalse) ((BTrue) (Some _ $ WkMatchable)))
  (let-match many (is-text s "names") (BFalse) ((BTrue) (Some _ $ WkNames)))
  (None _))

(def-fns _ $ (many repeated : (many (Raw) x) (subterm many (Nat) n) (many (List $ Raw) rest) -> (many (List $ Raw) r))
  (match many n _ ((Zero) rest) ((Succ k) (Cons _ x $ notail $ repeated x k rest))))

(def-fns _ $ (many next-arity : (many (Nat) a) (many (Nat) k) -> (many (Nat) r))
  (let-match many k (Succ _) ((Zero) 0))
  (match many (nat-cmp a k) _ ((CLt _ _ _ _ _) (Succ a)) (else 1)))

(def-fns _ $ (many wide-item : (many (WideKind) kind) (many (Pos) p) (many (Raw) ty) (many (Raw) field) (many (Raw) nm) (many (Nat) a) -> (many (Raw) r))
  (let ((many fields)) $ repeated (RawList p $ Cons _ (RawSymbol p (SName "many")) $ Cons _ field $ Cons _ (RawWild p) $ Nil _) a $ Cons _ (RawSymbol p (SName "->")) $ Cons _ (RawList p $ Cons _ ty $ Nil _) $ Nil _)
  (match many kind _
    ((WkCtors) (RawList p $ Cons _ (RawSymbol p (SName "many")) $ Cons _ nm $ Cons _ (RawSymbol p (SName ":")) fields))
    ((WkParams) (RawList p $ Cons _ (RawSymbol p (SName "erased")) $ Cons _ (RawList p $ Cons _ (RawSymbol p (SName "ValCtor")) fields) $ Cons _ nm $ Nil _))
    ((WkMatchable) (RawList p $ Cons _ (RawSymbol p (SName "many")) $ Cons _ nm $ Nil _))
    ((WkNames) nm)))

(def-fns _ $ (many wide-items : (many (WideKind) kind) (many (Pos) p) (many (Raw) ty) (many (Raw) field) (many (String) prefix)
    (many (Nat) k) (many (Nat) a) (many (Nat) i) (subterm many (Nat) n) -> (many (List $ Raw) r))
  (let-match many n (Succ m) ((Zero) (Nil _)))
  (let ((many nm)) $ RawSymbol p (SName (str-append prefix $ nat-str i)))
  (Cons _ (wide-item kind p ty field nm a) $ notail $ wide-items kind p ty field prefix k (next-arity a k) (Succ i) m))

(let ((many wide-usage)) "`(wide kind T P n k F)`, kind one of ctors, params, matchable, names")

(def-fns _ $ (many wide-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let-match many args (Cons _ kr r1) ((Nil _) (macro-fail mw here wide-usage)))
  (let-match many r1 (Cons _ ty r2) ((Nil _) (macro-fail mw here wide-usage)))
  (let-match many r2 (Cons _ pre r3) ((Nil _) (macro-fail mw here wide-usage)))
  (let-match many r3 (Cons _ nr r4) ((Nil _) (macro-fail mw here wide-usage)))
  (let-match many r4 (Cons _ ar r5) ((Nil _) (macro-fail mw here wide-usage)))
  (let-match many r5 (Cons _ field _) ((Nil _) (macro-fail mw here wide-usage)))
  (let ((unique mw1) (many n)) (arg-nat mw nr))
  (let ((unique mw3) (many k)) (arg-nat mw1 ar))
  (let-match many n (Some _ n2) ((None _) (macro-fail mw3 here wide-usage)))
  (let-match many k (Some _ k2) ((None _) (macro-fail mw3 here wide-usage)))
  (let-match many (kind-of $ sym-text kr) (Some _ kind) ((None _) (macro-fail mw3 here wide-usage)))
  (let ((many items)) $ wide-items kind here ty field (sym-text pre) k2 (next-arity k2 k2) 0 n2)
  (let-match many kind (WkMatchable) (else (values mw3 items)))
  (values mw3 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "Matchable")) $ Cons _ (RawSymbol here (SName "enum")) $ Cons _ ty items) $ Nil _))

(let ((many wide)) (MkMacro _ wide-fn))
