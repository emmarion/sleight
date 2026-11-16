(def-adts
  ((SelectA : (Type H) ((TyCtor (H h) ((Nat) a) ((Block) b) -> Type) Lk) (H h) ((Word) w)
              ((List (Code)) blocks) ((List (Code)) imms) ((Code) body) ((List (Word)) fields) -> Type)
    enum
    (many SelImmA : (erased Type H) (erased (TyCtor (H h) ((Nat) a) ((Block) b) -> Type) Lk) (erased H h) (erased (Nat) n)
       (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Code) body)
       (erased (Nth (Code) imms n body) br) -> (SelectA H Lk h (WImm n) blocks imms body (Nil (Word))))
    (many SelBlockA : (erased Type H) (erased (TyCtor (H h) ((Nat) a) ((Block) b) -> Type) Lk) (erased H h) (erased (Nat) p)
       (erased (List (Code)) blocks) (erased (List (Code)) imms) (erased (Code) body) (erased (Nat) tag) (erased (List (Word)) fs)
       (erased (Lk h p (MkBlock tag fs)) lk) (erased (Nth (Code) blocks tag body) br) -> (SelectA H Lk h (WAddr p) blocks imms body fs))))

(def-lvl laws)

(def-fns _ $ (erased select-fn-a : (erased Type H) (erased (TyCtor (H h) ((Nat) a) ((Block) b) -> Type) Lk)
    (erased (Fn laws (erased H h) (erased (Nat) a) (erased (Block) b1) (erased (Block) b2) (erased (Lk h a b1) p) (erased (Lk h a b2) q) ->
               (erased (Eq (Block) b1 b2) e)) lk-fn)
    (erased H h) (erased (Word) w) (erased (List (Code)) blocks imms) (erased (Code) body1 body2) (erased (List (Word)) fs1 fs2)
    (erased (SelectA H Lk h w blocks imms body1 fs1) d1) (erased (SelectA H Lk h w blocks imms body2 fs2) d2) ->
    (erased (Eq (Code) body1 body2) eb) (erased (Eq (List (Word)) fs1 fs2) ef))
  (match erased d1 _
    ((SelImmA _ _ _ n _ _ _ br1)
      (let-match erased d2 (SelImmA _ _ _ _ _ _ _ br2))
      (values (nth-fn _ imms n body1 body2 br1 br2) (Refl _ fs1)))
    ((SelBlockA _ _ _ p _ _ _ tag1 _ lk1 br1)
      (let-match erased d2 (SelBlockA _ _ _ _ _ _ _ tag2 _ lk2 br2))
      (let-match erased (lk-fn h p (MkBlock tag1 fs1) (MkBlock tag2 fs2) lk1 lk2) (Refl _ _))
      (values (nth-fn _ blocks tag1 body1 body2 br1 br2) (Refl _ fs1)))))

(def-fns laws $ (erased lookup-law : (erased (Heap) h) (erased (Nat) a) (erased (Block) b1) (erased (Block) b2)
    (erased (Lookup h a b1) p) (erased (Lookup h a b2) q) -> (erased (Eq (Block) b1 b2) e))
  (lookup-fn h a b1 b2 p q))

(def-fns _ $ (erased select-fn-list : (erased (Heap) h) (erased (Word) w) (erased (List (Code)) blocks imms) (erased (Code) body1 body2)
    (erased (List (Word)) fs1 fs2)
    (erased (SelectA (Heap) Lookup h w blocks imms body1 fs1) d1) (erased (SelectA (Heap) Lookup h w blocks imms body2 fs2) d2) ->
    (erased (Eq (Code) body1 body2) eb) (erased (Eq (List (Word)) fs1 fs2) ef))
  (select-fn-a (Heap) Lookup lookup-fn h w blocks imms body1 body2 fs1 fs2 d1 d2))
