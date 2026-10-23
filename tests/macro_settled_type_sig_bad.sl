; needs: ../std/macro
; error: argument 1, `a`, of `f`: type mismatch: expected `(List (Nat))`, got `(Nat)`
(let ((many xs)) (Cons (Nat) 1 $ Nil (Nat)))
(def-fns _ $ (many ty-fn : (unique (MacroWorld) mw) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawSettled here _ _ _ $ settled-type _ _ _ $ settled-of many xs) $ Nil _))
(let ((many ty)) (MkMacro _ ty-fn))
(def-fns _ $ (many f : (many (ty) a) -> (many (Nat) n)) 0)
(f 5)
; warns: tests/macro_settled_type_sig_bad.sl:4:71: warning: unused `args`; rename it `_args`
; warns: tests/macro_settled_type_sig_bad.sl:8:24: warning: unused `a`; rename it `_a`
