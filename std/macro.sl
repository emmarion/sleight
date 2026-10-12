(def-fns _ $ (many name : (many (Pos) p) (many (String) s) -> (many (Raw) r))
  (RawSymbol p (SName s)))

(def-fns _ $ (many nat-raw : (unique (MacroWorld) mw) (many (Pos) p) (many (Nat) n) -> (unique (MacroWorld) mw2 at mw) (many (Raw) r))
  (let ((unique mw1) (many h)) (intern-nat mw n))
  (values mw1 (RawSettled p _ _ _ h)))

(def-fns _ $ (many str-raw : (unique (MacroWorld) mw) (many (Pos) p) (many (String) s) -> (unique (MacroWorld) mw2 at mw) (many (Raw) r))
  (let ((unique mw1) (many h)) (intern-string mw s))
  (values mw1 (RawSettled p _ _ _ h)))

(let ((erased nat-type)) (Nat))

(def-fns _ $ (many arg-nat : (unique (MacroWorld) mw) (many (Raw) r) -> (unique (MacroWorld) mw2 at mw) (many (Maybe (Nat)) n))
  (let-match many r (RawSettled p m T t c) (else (values mw (None _))))
  (let-match many (settled-mult _ _ _ c) (MMany) (else (values mw (None _))))
  (let ((unique mw1) (many e)) (settled-eq _ _ _ _ _ _ mw (settled-type _ _ _ c) (settled-of erased nat-type)))
  (let-match many e (Some _ j) ((None _) (values mw1 (None _))))
  (let-match erased j (JMRefl _ _))
  (values mw1 (Some _ $ settled-value _ _ c)))

(def-fns _ $ (many form : (many (Pos) p) (many (List $ Raw) items) -> (many (Raw) r))
  (RawList p items))

(def-fns _ $ (many one : (many (Raw) a) -> (many (List $ Raw) out))
  (Cons _ a $ Nil _))

(def-fns _ $ (many two : (many (Raw) a) (many (Raw) b) -> (many (List $ Raw) out))
  (Cons _ a $ Cons _ b $ Nil _))

(def-fns _ $ (many three : (many (Raw) a) (many (Raw) b) (many (Raw) c) -> (many (List $ Raw) out))
  (Cons _ a $ Cons _ b $ Cons _ c $ Nil _))

(def-fns _ $ (many macro-fail : (unique (MacroWorld) mw) (many (Pos) p) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many m)) (str-raw mw p s))
  (values mw1 $ one $ form p $ two (RawSettled p _ _ _ (settled-of many compile-error)) m))

(def-fns _ $ (many same-sym : (many (Raw) a) (many (Raw) b) -> (many (Bool) r))
  (let-match many a (RawSymbol p x) (else (BFalse)))
  (let-match many b (RawSymbol q y) (else (BFalse)))
  (match many (symbol-eq x y) _ ((Some _ e) (BTrue)) ((None _) (BFalse))))

(def-fns _
  ((many same-raw : (subterm many (Raw) a) (many (Raw) b) -> (many (Bool) r))
    (let-match many a (RawList p xs) ((RawSymbol p x) (same-sym a b)) (else (BFalse)))
    (let-match many b (RawList q ys) (else (BFalse)))
    (tail $ same-raws xs ys))
  ((many same-raws : (subterm many (List $ Raw) xs) (many (List $ Raw) ys) -> (many (Bool) r))
    (match many xs _
      ((Nil _) (match many ys _ ((Nil _) (BTrue)) (else (BFalse))))
      ((Cons _ x xr)
        (let-match many ys (Cons _ y yr) ((Nil _) (BFalse)))
        (let-match many (notail $ same-raw x y) (BTrue) ((BFalse) (BFalse)))
        (tail $ same-raws xr yr)))))

(def-fns _ $ (many ref : (many (Pos) p) (erased Type T) (erased T t) (many (Settled (MErased) T t) h) -> (many (Raw) r))
  (RawSettled p _ _ _ h))

(def-fns _ $ (many app : (many (Pos) p) (many (Raw) f) (many (List $ Raw) args) -> (many (Raw) r))
  (form p $ Cons _ f args))
