; needs: ../std/macro ../std/tactics
; expect: "ok"
(def-fns _ $ (many gen-name : (unique (MacroWorld) mw) (many (Pos) p) (many (String) s) ->
    (unique (MacroWorld) mw2 at mw) (many (Raw) r))
  (let ((unique mw1) (many n) (erased g)) (gensym mw s))
  (values mw1 (RawSymbol p $ SGen n s g)))

(def-fns _ $ (many entry : (many (Pos) p) (many (String) m) (many (Raw) ty) (many (Raw) x) -> (many (Raw) r))
  (form p $ three (name p m) ty x))

(def-fns _ $ (many gen-chain-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many a)) (gen-name mw here "a"))
  (let ((unique mw2) (many b)) (gen-name mw1 here "b"))
  (let ((unique mw3) (many c)) (gen-name mw2 here "c"))
  (let ((unique mw4) (many h1)) (gen-name mw3 here "h"))
  (let ((unique mw5) (many h2)) (gen-name mw4 here "h"))
  (let ((unique mw6) (many r)) (gen-name mw5 here "r"))
  (let ((many nat)) (form here $ one $ name here "Nat"))
  (let ((many lt)) (name here "Lt"))
  (values mw6 $ one $ form here $ two (name here "lt-lemma") $ form here $
    Cons _ (name here "erased") $ Cons _ (name here "generated") $ Cons _ (name here ":") $
    Cons _ (entry here "erased" nat a) $ Cons _ (entry here "erased" nat b) $ Cons _ (entry here "erased" nat c) $
    Cons _ (entry here "erased" (form here $ three lt a b) h1) $ Cons _ (entry here "erased" (form here $ three lt b c) h2) $
    Cons _ (name here "->") $ one (entry here "erased" (form here $ three lt a (form here $ two (name here "Succ") c)) r)))
(let ((many gen-chain)) (MkMacro _ gen-chain-fn))

(gen-chain)
"ok"
