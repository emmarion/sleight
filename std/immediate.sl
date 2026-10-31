(def-adts
  ((Immediate : (Type A) -> Type)
    enum
    (many ImmU62 : -> (Immediate (U62)))
    (many ImmCopy : (erased Type A) (erased (Immediate A) p) -> (Immediate (Copy A)))
    (many ImmMaybe : (erased Type A) (erased (Immediate A) p) -> (Immediate (MaybeUninit A)))
    (many ImmUSlot : (erased Type A) (erased (Immediate A) p) -> (Immediate (USlotItem A)))))

(def-fns _ $ (erased imm-of : (erased Type A) (subterm erased (Immediate A) im) (erased A v) -> (erased (Imm A v) r))
  (match erased im _
    ((ImmU62)
      (let-match erased v (MkU62 n p))
      (ImmCoerce _ _ _ _ _ _ (coercible-wrap (Shared) MkU62 n p) (ImmNat n p)))
    ((ImmCopy B im1)
      (let-match erased v (MkCopy _ w))
      (ImmCoerce _ _ _ _ _ _ (coercible-wrap (Shared) MkCopy B w) (imm-of B im1 w)))
    ((ImmMaybe B im1)
      (match erased v _
        ((Vacant _ _) (ImmCoerce _ _ _ _ _ _ (coercible-wrap (Shared) Vacant B vacant-slot) (ImmVacant)))
        ((Stale _ s w q) (ImmCoerce _ _ _ _ _ _ (coercible-wrap (Shared) Stale B s w q) (ImmPlaced B w (imm-of B im1 w) s q)))
        ((Init _ x) (ImmCoerce _ _ _ _ _ _ (coercible-wrap (Shared) Init B x) (imm-of B im1 x)))))
    ((ImmUSlot B im1)
      (let-match erased v (MkUSlotItem _ s w q))
      (ImmCoerce _ _ _ _ _ _ (coercible-wrap (Shared) MkUSlotItem B s w q)
        (ImmFromSlot s B w (ImmPlaced B w (imm-of B im1 w) s q) q)))))

(def-fns _ $ (erased imm-all-of : (erased Type A) (erased (Immediate A) im) (subterm erased (List A) xs) -> (erased (ImmAll A xs) r))
  (match erased xs _
    ((Nil _) (ImmAllNil A))
    ((Cons _ x rest) (ImmAllCons A x rest (imm-of A im x) (imm-all-of A im rest)))))
