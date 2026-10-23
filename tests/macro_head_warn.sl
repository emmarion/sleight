; needs: ../std/macro
(def-fns _ $ (many if-zero-with : (many (Raw) head) (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (let-match many args (Cons _ n r1) ((Nil _) (Nil _)))
  (let-match many r1 (Cons _ a r2) ((Nil _) (Nil _)))
  (let-match many r2 (Cons _ b _) ((Nil _) (Nil _)))
  (Cons _ (RawList here $ Cons _ head $ Cons _ (RawSymbol here (SName "many")) $ Cons _ n $ Cons _ (RawWild here)
    $ Cons _ (RawList here $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "Zero")) $ Nil _) $ Cons _ a $ Nil _) $ Cons _ (RawList here $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "Succ")) $ Cons _ (RawWild here) $ Nil _) $ Cons _ b $ Nil _) $ Nil _) $ Nil _))
(def-fns _ $ (many if-zero-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ if-zero-with (RawSettled here _ _ _ (settled-of many match)) here args))
(let ((many if-zero)) (MkMacro _ if-zero-fn))
(def-fns _ $ (many if-zero-named-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ if-zero-with (RawSymbol here (SName "match")) here args))
(let ((many if-zero-named)) (MkMacro _ if-zero-named-fn))

(def-fns _ $ (many down-with : (many (Raw) head) (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (let-match many args (Cons _ f rest) ((Nil _) (Nil _)))
  (Cons _ (RawList here $ Cons _ f $ Cons _ (RawList here $ Cons _ head $ Cons _ (RawWild here) $ Nil _) rest) $ Nil _))
(def-fns _ $ (many down-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ down-with (RawSettled here _ _ _ (settled-of many predates)) here args))
(let ((many down)) (MkMacro _ down-fn))
(def-fns _ $ (many down-named-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ down-with (RawSymbol here (SName "predates")) here args))
(let ((many down-named)) (MkMacro _ down-named-fn))

(def-fns _ $ (many inc : (many (Nat) n) -> (many (Nat) m))
  (Succ n))

(def-fns _ $ (many pick : (many (Nat) n) -> (many (Nat) m))
  (if-zero n (Zero) $ match many (inc n) _ ((Zero) (Zero)) ((Succ j) j)))

(def-fns _ $ (many pick-named : (many (Nat) n) -> (many (Nat) m))
  (if-zero-named n (Zero) $ match many (inc n) _ ((Zero) (Zero)) ((Succ j) j)))

(def-fns _ $ (many thrice : (many (Nat) n) -> (many (Nat) m))
  (let ((many a)) (down inc n))
  (let ((many b)) (down-named inc a))
  (down inc $ inc (predates _) b))

(Cons _ (pick 3) $ Cons _ (pick-named 0) $ Cons _ (thrice 1) $ Nil _)
; expect: (Cons _ 3 $ Cons _ 0 $ Cons _ 5 $ Nil _)
; warns: tests/macro_head_warn.sl:36:3: warning: lopsided `match`; flatten it with a `let-match` on `Succ`
; warns: tests/macro_head_warn.sl:36:3: note: in the expansion of `if-zero-named` here
; warns: tests/macro_head_warn.sl:40:19: warning: unnecessary `(predates _)`; drop it
; warns: tests/macro_head_warn.sl:40:19: note: in the expansion of `down-named` here
; warns: tests/macro_head_warn.sl:41:19: warning: unnecessary `(predates _)`; drop it
; warns: tests/macro_head_warn.sl:41:3: note: in the expansion of `down` here
