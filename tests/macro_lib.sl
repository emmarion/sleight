; needs: ../std/macro
(def-fns _ $ (many splice-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw args))
(let ((many splice)) (MkMacro _ splice-fn))

(def-fns _ $ (many swap-out : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (let-match many args (Cons _ f r1) ((Nil _) (Nil _)))
  (let-match many r1 (Cons _ a r2) ((Nil _) (Nil _)))
  (let-match many r2 (Cons _ b _) ((Nil _) (Nil _)))
  (Cons _ (RawList here $ Cons _ f $ Cons _ b $ Cons _ a $ Nil _) $ Nil _))
(def-fns _ $ (many swap-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ swap-out here args))
(let ((many swap)) (MkMacro _ swap-fn))

(def-fns _ $ (many warn-at : (unique (MacroWorld) mw at vacant-slot) (many (Pos) p) (many (String) s) -> (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many m)) (str-raw mw p s))
  (values mw1 $ Cons _ (RawList p $ Cons _ (RawSymbol p (SName "compile-warn")) $ Cons _ m $ Nil _) $ Nil _))

(def-fns _ $ (many warn-here-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (warn-at mw here "here"))
(let ((many warn-here)) (MkMacro _ warn-here-fn))

(def-fns _ $ (many warn-nowhere-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (warn-at mw (NoPos) "nowhere"))
(let ((many warn-nowhere)) (MkMacro _ warn-nowhere-fn))

(def-fns _ $ (many warn-zero-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (warn-at mw (MkPos "" 0 0) "zero"))
(let ((many warn-zero)) (MkMacro _ warn-zero-fn))

(def-fns _ $ (many warn-elsewhere-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (warn-at mw (MkPos "elsewhere.sl" 7 9) "elsewhere"))
(let ((many warn-elsewhere)) (MkMacro _ warn-elsewhere-fn))

(def-fns _ $ (many line-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (match many here _
    ((NoPos) (let ((unique mw1) (many r)) (nat-raw mw here 0)) (values mw1 $ Cons _ r $ Nil _))
    ((MkPos _ l _) (let ((unique mw1) (many r)) (nat-raw mw here l)) (values mw1 $ Cons _ r $ Nil _))))
(let ((many line)) (MkMacro _ line-fn))

(def-fns _ $ (many loop-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "loop")) $ Nil _) $ Nil _))
(let ((many loop)) (MkMacro _ loop-fn))
