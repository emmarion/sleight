(def-adts $ (Imp : (Type A) (Type B) -> Type)
  enum
  (many MkImp : (erased Type A) (erased Type B) (erased (Level) K) (erased (Fn K (erased A a) -> (erased B b)) f) -> (Imp A B)))
(def-lvl M)
(def-lvl L)
(def-fns L $ (erased s-inner : (erased Type A) (erased Type B) (erased Type C)
    (erased (Fn M (erased A a) -> (erased (Imp B C) k)) f) (erased (Fn M (erased A a) -> (erased B b)) g) (erased A x) ->
    (erased C c))
  (let-match erased (f x) (MkImp _ _ K h))
  (h $ g x))
