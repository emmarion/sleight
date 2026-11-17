(def-adts $ (Imp : (Type A) (Type B) -> Type)
  enum
  (many MkImp : (erased Type A) (erased Type B) (erased (Level) K) (erased (Fn K (erased A a) -> (erased B b)) f) -> (Imp A B)))
(def-fns _ $ (erased compose : (erased Type A) (erased Type B) (erased Type C) (erased (Imp A B) g) (erased (Imp B C) h) ->
    (erased (Imp A C) r))
  (let-match erased g (MkImp _ _ KG fg))
  (let-match erased h (MkImp _ _ KH fh))
  (def-lvl N)
  (def-fns N $ (erased gh : (erased A a) -> (erased C c))
    (fh $ fg a))
  (MkImp A C N gh))
