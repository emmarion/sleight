; needs: ../std/macro macro_lib
; expect: (MkPair _ _ (MkPair _ _ 7 7) $ MkPair _ _ 7 7)
(def-fns _ $ (many pair : (many (Pos) p) (many (Raw) a) (many (Raw) b) -> (many (Raw) r))
  (form p $ Cons _ (name p "MkPair") $ Cons _ (RawWild p) $ Cons _ (RawWild p) $ two a b))
(def-fns _ $ (many twice-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (intern-nat mw 7))
  (let ((unique mw2) (many g)) (intern-nat mw1 (nat-add 3 4)))
  (let ((unique mw3) (many vh)) (nat-raw mw2 here $ settled-value _ _ h))
  (let ((unique mw4) (many vg)) (nat-raw mw3 here $ settled-value _ _ g))
  (values mw4 $ one $ pair here (pair here vh vg)
    (pair here (RawSettled here _ _ _ h) (RawSettled here _ _ _ g))))
(let ((many twice)) (MkMacro _ twice-fn))
(twice)
