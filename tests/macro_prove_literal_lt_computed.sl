; needs: ../std/macro macro_lib
; expect: "ok"
; prove-literal-lt takes any Settled `many` Nat, not only a literal: k is computed.
(let ((many k)) (nat-add 2 3))
(def-fns _ $ (many lt-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many nine)) (nat-raw mw here 9))
  (values mw1 $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "prove-literal-lt")) $ Cons _ (RawSettled here _ _ _ (settled-of many k)) $ Cons _ nine $ Nil _) $ Nil _))
(let ((many lt)) (MkMacro _ lt-fn))
(let ((erased (Lt k 9) p)) (lt))
"ok"
