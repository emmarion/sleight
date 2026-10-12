; needs: ../std/macro macro_lib
; expect: (MkPair _ _ 16 $ MkPair _ _ "a\nb" 3)
(def-fns _ $ (many line-of : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (match many here _
    ((NoPos) (let ((unique mw1) (many r)) (nat-raw mw (NoPos) 0)) (values mw1 $ one r))
    ((MkPos f ln col) (let ((unique mw1) (many r)) (nat-raw mw (NoPos) ln)) (values mw1 $ one r))))
(def-fns _ $ (many text : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many r)) (str-raw mw here "a\nb"))
  (values mw1 $ one r))
(def-fns _ $ (many succ : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ RawList here $ Cons _ (name (NoPos) "Succ") args))
(let ((many line-m) (many str) (many inc)) (values (MkMacro _ line-of) (MkMacro _ text) (MkMacro _ succ)))
(let ((many n)) (line-m))
(MkPair _ _ n $ MkPair _ _ (str) (inc 2))
