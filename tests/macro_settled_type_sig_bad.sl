; needs: ../std/macro
; error: argument 1, `a`, of `f`: type mismatch: expected `(List (Nat))`, got `(Nat)`
(let ((many xs)) (Cons (Nat) 1 $ Nil (Nat)))
(def-fns _ $ (many ty-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ one $ RawSettled here _ _ _ $ settled-type _ _ _ $ settled-of many xs))
(let ((many ty)) (MkMacro _ ty-fn))
(def-fns _ $ (many f : (many (ty) a) -> (many (Nat) n)) 0)
(f 5)
