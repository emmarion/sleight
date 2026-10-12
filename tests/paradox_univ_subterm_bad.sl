; error: `Type` is not a strict subterm of `Type`
(def-adts $ (Box : (Type A) -> Type)
  enum
  (many MkBox : (erased Type A) (erased A a) -> (Box A)))
(let ((erased t)) (MkBox Type Type))
(let ((erased p)) (prove-subterm Type (MkBox Type Type)))
(let ((erased q)) (prove-subterm Type Type))
