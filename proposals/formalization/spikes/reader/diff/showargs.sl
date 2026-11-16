(def-fns _ $ (many symbol-text : (many (Symbol) s) -> (many (String) t))
  (match many s _ ((SName t) t) ((SGen _ t _) t)))

(def-fns _
  ((many raw-show : (subterm many (Raw) r) -> (many (Rope) out))
    (match many r _
      ((RawSymbol _ s) (RStr $ symbol-text s))
      ((RawWild _) (RStr "_"))
      ((RawList _ items) (RCat (RStr "(") $ RCat (notail $ raws-show items) $ RStr ")"))
      ((RawSettled _ _ _ _ _) (RStr "<literal>"))))
  ((many raws-show : (subterm many (List $ Raw) rs) -> (many (Rope) out))
    (let-match many rs (Cons _ r rest) ((Nil _) (REmpty)))
    (let-match many rest (Cons _ _ _) ((Nil _) (tail $ raw-show r)))
    (RCat (notail $ raw-show r) $ RCat (RStr " ") $ notail $ raws-show rest)))

(def-fns _ $ (many show-args-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) _here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((many s) (erased _)) (flatten $ raws-show args))
  (let ((unique mw1) (many h)) (intern-string mw s))
  (values mw1 $ Cons _ (RawSettled (NoPos) _ _ _ h) $ Nil _))

(let ((many show-args)) (MkMacro _ show-args-fn))
