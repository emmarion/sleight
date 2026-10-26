; needs: ../std/macro ../std/nat ../std/tactics
; expect: "ok"
(def-fns _ $ (many gen-name : (unique (MacroWorld) mw at vacant-slot) (many (Pos) p) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Raw) r))
  (let ((unique mw1) (many n) (erased g)) (gensym mw s))
  (values mw1 (RawSymbol p $ SGen n s g)))

(def-fns _ $ (many entry : (many (Pos) p) (many (String) m) (many (Raw) ty) (many (Raw) x) -> (many (Raw) r))
  (RawList p $ Cons _ (RawSymbol p (SName m)) $ Cons _ ty $ Cons _ x $ Nil _))

(def-fns _ $ (many gen-chain-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many a)) (gen-name mw here "a"))
  (let ((unique mw2) (many b)) (gen-name mw1 here "b"))
  (let ((unique mw3) (many c)) (gen-name mw2 here "c"))
  (let ((unique mw4) (many h1)) (gen-name mw3 here "h"))
  (let ((unique mw5) (many h2)) (gen-name mw4 here "h"))
  (let ((unique mw6) (many r)) (gen-name mw5 here "r"))
  (let ((many nat)) (RawList here $ Cons _ (RawSymbol here (SName "Nat")) $ Nil _))
  (let ((many lt)) (RawSymbol here (SName "Lt")))
  (values mw6 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "lt-lemma")) $ Cons _ (RawList here $
    Cons _ (RawSymbol here (SName "erased")) $ Cons _ (RawSymbol here (SName "generated")) $ Cons _ (RawSymbol here (SName ":")) $
    Cons _ (entry here "erased" nat a) $ Cons _ (entry here "erased" nat b) $ Cons _ (entry here "erased" nat c) $
    Cons _ (entry here "erased" (RawList here $ Cons _ lt $ Cons _ a $ Cons _ b $ Nil _) h1) $ Cons _ (entry here "erased" (RawList here $ Cons _ lt $ Cons _ b $ Cons _ c $ Nil _) h2) $
    Cons _ (RawSymbol here (SName "->")) $ Cons _ (entry here "erased" (RawList here $ Cons _ lt $ Cons _ a $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "Succ")) $ Cons _ c $ Nil _) $ Nil _) r) $ Nil _) $ Nil _) $ Nil _))
(let ((many gen-chain)) (MkMacro _ gen-chain-fn))

(gen-chain)
"ok"
