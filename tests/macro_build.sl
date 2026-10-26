; needs: ../std/macro macro_lib
; expect: (MkPair _ _ 16 $ MkPair _ _ "a\nb" 3)
(def-fns _ $ (many line-of : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (match many here _
    ((NoPos) (let ((unique mw1) (many r)) (nat-raw mw (NoPos) 0)) (values mw1 $ Cons _ r $ Nil _))
    ((MkPos _ ln _) (let ((unique mw1) (many r)) (nat-raw mw (NoPos) ln)) (values mw1 $ Cons _ r $ Nil _))))
(def-fns _ $ (many text : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many r)) (str-raw mw here "a\nb"))
  (values mw1 $ Cons _ r $ Nil _))
(def-fns _ $ (many succ : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSymbol (NoPos) (SName "Succ")) args) $ Nil _))
(let ((many line-m) (many str) (many inc)) (values (MkMacro _ line-of) (MkMacro _ text) (MkMacro _ succ)))
(let ((many n)) (line-m))
(MkPair _ _ n $ MkPair _ _ (str) (inc 2))
