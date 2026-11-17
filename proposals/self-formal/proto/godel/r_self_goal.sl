(def-adts $ (Prov : ((String) s) -> Type)
  enum
  (many MkProv : (erased (String) s) -> (Prov s)))
(def-fns _ $ (many own-text : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) ->
    (unique (MacroWorld) mw2 at mw) (many (Raw) t))
  (let-match many here (MkPos file _ _) (else (fail-raw mw here "no position")))
  (let ((unique mw1) (many r)) (read-file mw here file))
  (let-match many r (Ok _ text) ((Fail _ m) (fail-raw mw1 here m)))
  (str-raw mw1 here text))
(def-fns _ $ (many wrap : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (String) head) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many t)) (own-text mw here))
  (values mw1 $ Cons _ (RawList here $ Cons _ (RawSymbol here $ SName head) $ Cons _ t $ Nil _) $ Nil _))
(def-fns _ $ (many prov-self-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (wrap mw here "Prov"))
(def-fns _ $ (many mk-self-fn : (unique (MacroWorld) mw at vacant-slot) (many (Pos) here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (wrap mw here "MkProv"))
(let ((many prov-self)) (MkMacro _ prov-self-fn))
(let ((many mk-self)) (MkMacro _ mk-self-fn))
(goal erased (prov-self))
(qed (mk-self))
