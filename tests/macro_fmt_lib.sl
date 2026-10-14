; needs: ../std/macro
(def-adts $ (Fmt : -> Type)
  enum
  (many FmtLit : (many (Raw) r) -> (Fmt))
  (many FmtNat : -> (Fmt))
  (many FmtStr : -> (Fmt)))

(def-fns _ $ (many rope-str : (many (Rope) r) -> (many (String) s))
  (let ((many s) (erased p)) (flatten r))
  s)

(def-fns _ $ (many char-is : (many (Char) c) (many (Char) d) -> (many (Bool) b))
  (match many (char-cmp c d) _ ((CEq _ _ _) (BTrue)) (else (BFalse))))

(def-fns _ $ (many hole : (many (Char) d) -> (many (Maybe $ Fmt) k))
  (let-match many (char-is d #\n) (BFalse) ((BTrue) (Some _ $ FmtNat)))
  (let-match many (char-is d #\s) (BFalse) ((BTrue) (Some _ $ FmtStr)))
  (None _))

(def-fns _ $ (many one-fmt : (many (Fmt) f) -> (many (List $ Fmt) fs))
  (Cons _ f $ Nil _))

(def-fns _ $ (many parse-fmt : (unique (MacroWorld) mw) (many (Pos) here) (subterm many (String) s) (many (Rope) acc) ->
    (unique (MacroWorld) mw2 at mw) (many (Maybe $ List $ Fmt) r))
  (let ((unique mw1) (many lit)) (str-raw mw here $ rope-str acc))
  (let-match many s (SCons c rest) ((SNil) (values mw1 (Some _ $ one-fmt $ FmtLit lit))))
  (let-match many (char-is c #\~) (BTrue) ((BFalse) (tail $ parse-fmt mw1 here rest $ RCat acc $ RChar c)))
  (let-match many rest (SCons d rest2) ((SNil) (values mw1 (None _))))
  (let-match many (char-is d #\~) (BFalse) ((BTrue) (tail $ parse-fmt mw1 here rest2 $ RCat acc $ RChar d)))
  (let-match many (hole d) (Some _ k) ((None _) (values mw1 (None _))))
  (let ((unique mw2) (many m)) (notail $ parse-fmt mw1 here rest2 (REmpty)))
  (let-match many m (Some _ fs) ((None _) (values mw2 (None _))))
  (values mw2 $ Some _ $ Cons _ (FmtLit lit) $ Cons _ k fs))

(def-fns _ $ (many fill : (many (Pos) p) (many (Fmt) f) (many (List $ Raw) args) -> (many (Maybe $ Raw) str) (many (List $ Raw) more))
  (match many f _
    ((FmtLit r) (values (Some _ r) args))
    (else (match many args _
      ((Nil _) (values (None _) args))
      ((Cons _ a more) (values (Some _ $ match many f (((Raw) x))
          ((FmtNat) (form p $ two (ref p _ _ _ (settled-of many nat-str)) a))
          (else a))
        more))))))

(def-fns _ $ (many render : (many (Pos) p) (subterm many (List $ Fmt) fs) (many (List $ Raw) args) -> (many (Maybe $ Raw) r))
  (let-match many fs (Cons _ f rest)
    ((Nil _) (match many args _ ((Nil _) (Some _ $ form p $ one $ ref p _ _ _ (settled-of many REmpty))) (else (None _)))))
  (let ((many ms) (many more)) (fill p f args))
  (let-match many ms (Some _ str) ((None _) (None _)))
  (let-match many (notail $ render p rest more) (Some _ t) ((None _) (None _)))
  (Some _ $ form p $ three (ref p _ _ _ (settled-of many RCat)) (form p $ two (ref p _ _ _ (settled-of many RStr)) str) t))

(let ((erased macro-type)) (Macro))

(def-fns _ $ (many fmt-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let-match many args (Cons _ a _) ((Nil _) (macro-fail mw here "fmt: expected a format string")))
  (let ((unique mw0) (many ms)) (arg-string mw a))
  (let-match many ms (Some _ s) ((None _) (macro-fail mw0 here "fmt: expected a format string")))
  (let ((unique mw1) (many mfs)) (parse-fmt mw0 here s (REmpty)))
  (let-match many mfs (Some _ fs) ((None _) (macro-fail mw1 here "fmt: a `~` must be followed by `n`, `s` or `~`")))
  (def-fns _ $ (many apply-fn : (unique (MacroWorld) aw) (many (Pos) at-here) (many (List $ Raw) xs) ->
      (unique (MacroWorld) aw2 at aw) (many (List $ Raw) o))
    (let-match many (render at-here fs xs) (Some _ t) ((None _) (macro-fail aw at-here "fmt: wrong number of arguments")))
    (values aw $ one $ form at-here $ two (ref at-here _ _ _ (settled-of many rope-str)) t))
  (let ((unique mw2) (many h)) (mint-settled mw1 _ (settled-of erased macro-type) (MkMacro _ apply-fn)))
  (values mw2 $ one $ RawSettled here _ _ _ h))
(let ((many fmt)) (MkMacro _ fmt-fn))
