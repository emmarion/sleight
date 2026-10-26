; needs: ../std/macro macro_lib
; expect: (MkPair _ _ 102 $ MkPair _ _ 7 $ MkPair _ _ 5 6)
; warns: <**>:19:24: warning: declaration of `nat-add` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
; warns: <**>:19:45: warning: declaration of `k` shadows a previous binder
; warns: <**>:13:7: note: shadowed binder is here
; warns: <**>:19:24: warning: unused `nat-add`; rename it `_nat-add`
; warns: <**>:21:7: warning: declaration of `k` shadows a previous binder
; warns: <**>:13:7: note: shadowed binder is here
; warns: <**>:34:7: warning: declaration of `let` shadows a built-in
; warns: <**>:35:13: warning: declaration of `Nat` shadows a previous binder
; warns: lib/prelude.sl:<**>: note: shadowed binder is here
(let ((many k)) 100)
(def-fns _ $ (many plus-k-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many h)) nat-add)
  (values mw $ Cons _ (RawList here $ Cons _ (RawSettled here _ _ _ (settled-of many h)) $ Cons _ (RawSettled here _ _ _ (settled-of many k)) args) $ Nil _))
(let ((many plus-k)) (MkMacro _ plus-k-fn))
(def-fns _ $ (many f : (many (Nat) nat-add) (many (Nat) k) -> (many (Nat) r))
  (plus-k k))
(let ((many k)) 5)

(def-fns _ $ (many seven-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw9) (many lit)) (nat-raw mw here 7))
  (values mw9 $ Cons _ (RawList here $ Cons _ (RawSettled here _ _ _ (settled-of many let)) $ Cons _ (RawList here $ Cons _ (RawList here $ Cons _ (RawSymbol here (SName "many")) $ Cons _ (RawSymbol here (SName "x")) $ Nil _) $ Nil _) $ Cons _ lit $ Nil _) $ Nil _))
(let ((many seven)) (MkMacro _ seven-fn))

(def-fns _ $ (many nat-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (values mw $ Cons _ (RawList here $ Cons _ (RawSettled here _ _ _ (settled-of erased Nat)) $ Nil _) $ Nil _))
(let ((many PNat)) (MkMacro _ nat-fn))

(let ((many let)) 0)
(def-adts $ (Nat : -> Type) enum (many Z : -> (Nat)))
(def-fns _ $ (many g : (many (PNat) n) -> (many (PNat) r)) (nat-add n 1))
(seven)
(MkPair _ _ (f 1 2) $ MkPair _ _ x $ MkPair _ _ k (g k))
