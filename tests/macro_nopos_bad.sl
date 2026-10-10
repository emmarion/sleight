; error: expected `(Nat)`
(def-fns _ $ (many one : (many (Raw) r) -> (many (List $ Raw) out)) (Cons _ r $ Nil _))
(def-fns _ $ (many m : (many (Pos) here) (many (List $ Raw) args) -> (many (List $ Raw) out))
  (one $ RawList (NoPos) $ Cons _ (RawName (NoPos) "Succ") $ Cons _ (RawStr (NoPos) "x") $ Nil _))
(let ((many mac)) (MkMacro _ m))
(mac)
