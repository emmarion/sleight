; needs: ../std/macro
; expect: (MkPair _ _ 0 $ MkPair _ _ (Cons _ 1 $ Nil _) $ MkPair _ _ (Cons _ 1 $ Nil _) $ Cons _ 1 $ Nil _)
(let ((many xs)) (Cons (Nat) 1 $ Nil (Nat)))
(def-fns _ $ (many ty-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawSettled here _ _ _ $ settled-type _ _ _ $ settled-of many xs) $ Nil _))
(let ((many ty)) (MkMacro _ ty-fn))
(def-fns _ $ (many f : (many (ty) _a) -> (many (Nat) n)) 0)
(def-fns _ $ (many g : (many (Nat) _k) -> (many (ty) a)) xs)
(def-adts $ (W : -> Type) enum (many MkW : (many (ty) a) -> (W)))
(let-match many (MkW xs) (MkW w))
(def-fns _ $ (many h : (many (Bool) b) -> (many (List (Nat)) r)) (match many b (((ty) t)) ((BTrue) xs) ((BFalse) (Nil _))))
(MkPair _ _ (f xs) $ MkPair _ _ (g 0) $ MkPair _ _ w (h (BTrue)))
