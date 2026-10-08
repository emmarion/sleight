(def-fns _ $ (erased u62-list-witness : (erased (List (Nat)) xs) (subterm erased (AllBelow (Nat) Lt xs u62-modulus) small) ->
    (erased (List (U62)) us)
    (erased (Coercible (Shared) (List (Nat)) xs (Shared) (List (U62)) us) c))
  (let-match erased small (BelowCons _ _ x rest _ p small1)
    ((BelowNil _ _ _) (values (Nil (U62)) (coercible-ctor (Shared) Nil (Nat) (U62)))))
  (let ((erased us1) (erased c1)) (u62-list-witness rest small1))
  (values (Cons (U62) (MkU62 x p) us1)
          (coercible-ctor (Shared) Cons (Nat) (U62) (coercible-wrap (Shared) MkU62 x p) c1)))
