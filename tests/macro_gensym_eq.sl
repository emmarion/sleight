; expect: (MkPair _ _ "same" "different")
(def-fns _ $ (many gen-eq : (many (Nat) n) (erased (String) s) (erased (Gensym n s) g)
    (many (Nat) m) (erased (String) t) (erased (Gensym m t) h) ->
    (many (Maybe $ Eq (Raw) (RawSymbol (NoPos) (SGen n s g)) (RawSymbol (NoPos) (SGen m t h))) r))
  (let-match many (nat-cmp n m) (CEq _ _ _) (else (None _)))
  (let-match erased (gensym-unique _ _ _ g h) (JMRefl _ _))
  (Some _ $ Refl _ _))
(def-fns _ $ (many verdict : (many (Nat) n) (erased (String) s) (erased (Gensym n s) g)
    (many (Nat) m) (erased (String) t) (erased (Gensym m t) h) -> (many (String) out))
  (match many (gen-eq n s g m t h) _
    ((Some _ _) "same")
    ((None _) "different")))
(def-fns _ $ (many cmp-fn : (unique (MacroWorld) mw) (many (Pos) _here) (many (List $ Raw) args) ->
    (unique (MacroWorld) mw2 at mw) (many (List $ Raw) out))
  (let ((unique mw1) (many a) (erased ga)) (gensym mw "x"))
  (let ((unique mw2) (many b) (erased gb)) (gensym mw1 "x"))
  (let ((unique mw3) (many v)) $ intern-string mw2 $ match many args _
    ((Nil _) (verdict a "x" ga a "x" ga))
    ((Cons _ _ _) (verdict a "x" ga b "x" gb)))
  (values mw3 $ Cons _ (RawSettled (NoPos) _ _ _ v) $ Nil _))
(let ((many cmp)) (MkMacro _ cmp-fn))
(MkPair _ _ (cmp) (cmp 0))
