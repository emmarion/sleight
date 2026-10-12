(def-adts
  ((Box : -> Type)
    enum
    (many MkBox : (erased Type T) (erased T x) -> (Box))))
(def-lvl L)
(def-fns L $ (erased id : (erased Type A) (erased A x) -> (erased A y))
  x)
(let ((erased t)) (id Type (Nat)))
(MkBox Type (id Type t))
