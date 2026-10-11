; error: argument 2, `a`, of `Some`: type mismatch
(def-fns _ $ (many gen-eq : (many (Nat) n) (many (String) s) (erased (Gensym n s) g)
    (many (Nat) m) (many (String) t) (erased (Gensym m t) h) ->
    (many (Maybe $ Eq (Raw) (RawGen (NoPos) n s g) (RawGen (NoPos) m t h)) r))
  (let-match many (nat-cmp n m) (CEq _ _ _) (else (None _)))
  (Some _ $ Refl _ _))
