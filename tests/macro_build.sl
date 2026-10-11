; expect: (MkPair _ _ 15 $ MkPair _ _ "a\nb" 3)
(def-fns _ $ (many one : (many (Raw) r) -> (many (List $ Raw) out)) (Cons _ r $ Nil _))
(def-fns _ $ (many line-of : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (match many here _
    ((NoPos) (values mw $ one $ RawNat (NoPos) 0))
    ((MkPos f line col) (values mw $ one $ RawNat (NoPos) line))))
(def-fns _ $ (many text : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ RawStr here "a\nb"))
(def-fns _ $ (many succ : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ RawList here $ Cons _ (RawName (NoPos) "Succ") args))
(let ((many line) (many str) (many inc)) (values (MkMacro _ line-of) (MkMacro _ text) (MkMacro _ succ)))
(let ((many n)) (line))
(MkPair _ _ n $ MkPair _ _ (str) (inc 2))
