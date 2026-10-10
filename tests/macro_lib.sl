(def-fns _ $ (many name : (many (Pos) p) (many (String) s) -> (many (Raw) r))
  (RawName p s))

(def-fns _ $ (many form : (many (Pos) p) (many (List $ Raw) items) -> (many (Raw) r))
  (RawList p items))

(def-fns _ $ (many one : (many (Raw) a) -> (many (List $ Raw) out))
  (Cons _ a $ Nil _))

(def-fns _ $ (many two : (many (Raw) a) (many (Raw) b) -> (many (List $ Raw) out))
  (Cons _ a $ Cons _ b $ Nil _))

(def-fns _ $ (many three : (many (Raw) a) (many (Raw) b) (many (Raw) c) -> (many (List $ Raw) out))
  (Cons _ a $ Cons _ b $ Cons _ c $ Nil _))

(def-fns _ $ (many splice-fn : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  args)
(let ((many splice)) (MkMacro _ splice-fn))

(def-fns _ $ (many swap-fn : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (let-match many args (Cons _ f r1) ((Nil _) (Nil _)))
  (let-match many r1 (Cons _ a r2) ((Nil _) (Nil _)))
  (let-match many r2 (Cons _ b r3) ((Nil _) (Nil _)))
  (one $ form here $ three f b a))
(let ((many swap)) (MkMacro _ swap-fn))

(def-fns _ $ (many warn-at : (many (Pos) p) (many (String) s) -> (many (List $ Raw) out))
  (one $ form p $ two (name p "compile-warn") (RawStr p s)))

(def-fns _ $ (many warn-here-fn : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (warn-at here "here"))
(let ((many warn-here)) (MkMacro _ warn-here-fn))

(def-fns _ $ (many warn-nowhere-fn : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (warn-at (NoPos) "nowhere"))
(let ((many warn-nowhere)) (MkMacro _ warn-nowhere-fn))

(def-fns _ $ (many warn-zero-fn : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (warn-at (MkPos "" 0 0) "zero"))
(let ((many warn-zero)) (MkMacro _ warn-zero-fn))

(def-fns _ $ (many warn-elsewhere-fn : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (warn-at (MkPos "elsewhere.sl" 7 9) "elsewhere"))
(let ((many warn-elsewhere)) (MkMacro _ warn-elsewhere-fn))

(def-fns _ $ (many line-fn : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (match many here _
    ((NoPos) (one $ RawNat here 0))
    ((MkPos f l c) (one $ RawNat here l))))
(let ((many line)) (MkMacro _ line-fn))

(def-fns _ $ (many loop-fn : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (one $ form here $ one $ name here "loop"))
(let ((many loop)) (MkMacro _ loop-fn))
