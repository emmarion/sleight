; needs: ../std/macro macro_fmt_lib
; expect: "<7>"
(let ((erased special-type)) (Special))
(def-fns _ $ (many minted-let-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) _args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many h)) (mint-settled mw _ (settled-of erased special-type) let))
  (values mw1 $ Cons _ (RawSettled here _ _ _ h) $ Nil _))
(let ((many minted-let)) (MkMacro _ minted-let-fn))
(def-fns _ $ (many as-macro : (erased (JMEq Type (Level) Type (Macro)) e) (many (Nat) x) -> (many (String) s))
  (let-match erased e (JMRefl _ _))
  ((fmt "<~n>") x))
(def-fns _ $ (many as-special : (erased (JMEq Type (Level) Type (Special)) e) (many (Nat) x) -> (many (Nat) y))
  (let-match erased e (JMRefl _ _))
  ((minted-let) ((many z)) x)
  z)
((fmt "<~n>") 7)
