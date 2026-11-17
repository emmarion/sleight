(def-adts $ (Imp : (Type A) (Type B) -> Type)
  enum
  (many MkImp : (erased Type A) (erased Type B) (erased (Level) K) (erased (Fn K (erased A a) -> (erased B b)) f) -> (Imp A B)))
(def-fns _ $ (erased mp : (erased Type A) (erased Type B) (erased (Imp A B) h) (erased A x) -> (erased B y))
  (let-match erased h (MkImp _ _ K f))
  (f x))
